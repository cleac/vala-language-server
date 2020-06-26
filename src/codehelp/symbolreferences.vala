using LanguageServer;
using Gee;

/** 
 * Contains routines for analyzing references to symbols across the project.
 * Used by `textDocument/definition`, `textDocument/rename`, `textDocument/prepareRename`,
 * `textDocument/references`, and `textDocument/documentHighlight`.
 */
namespace Vls.SymbolReferences {
    /**
     * Find a symbol in ``context`` matching ``symbol`` or ``null``.
     *
     * @param context       the {@link Vala.CodeContext} to search for a matching symbol in
     * @param symbol        the symbol to match, which comes from a different {@link Vala.CodeContext}
     * @return              the matching symbol in ``context``, or ``null`` if one could not be found
     */
    public Vala.Symbol? find_matching_symbol (Vala.CodeContext context, Vala.Symbol symbol) {
        var symbols = new GLib.Queue<Vala.Symbol> ();
        Vala.Symbol? matching_sym = null;

        // walk up the symbol hierarchy to the root
        for (Vala.Symbol? current_sym = symbol;
             current_sym != null && current_sym.name != null && current_sym.to_string () != "(root namespace)";
             current_sym = current_sym.parent_symbol) {
            symbols.push_head (current_sym);
        }

        matching_sym = context.root.scope.lookup (symbols.pop_head ().name);
        while (!symbols.is_empty () && matching_sym != null) {
            var parent_sym = matching_sym;
            var symtab = parent_sym.scope.get_symbol_table ();
            if (symtab != null) {
                var current_sym = symbols.pop_head ();
                matching_sym = symtab[current_sym.name];
                string? gir_name = null;
                // look for the GIR version of current_sym instead
                if (matching_sym == null && (gir_name = current_sym.get_attribute_string ("GIR", "name")) != null) {
                    matching_sym = symtab[gir_name];
                    if (matching_sym != null && matching_sym.source_reference.file.file_type != Vala.SourceFileType.PACKAGE)
                        matching_sym = null;
                }
            } else {
                // workaround: "GLib" namespace may be empty when dealing with GLib-2.0.gir (instead, "G" namespace will be populated)
                if (matching_sym.name == "GLib") {
                    matching_sym = context.root.scope.lookup ("G");
                } else 
                    matching_sym = null;
            }
        }

        if (!symbols.is_empty ())
            return null;

        return matching_sym;
    }


    /**
     * Gets the symbol you really want, not something from a generated file.
     *
     * If `symbol` comes from a generated file (eg. a VAPI), then
     * it would be more useful to show the file specific to the compilation
     * that generated the file.
     */
    Vala.Symbol find_real_symbol (Project project, Vala.Symbol symbol) {
        if (symbol.source_reference == null || symbol.source_reference.file == null)
            return symbol;

        Compilation alter_comp;
        if (project.lookup_compilation_for_output_file (symbol.source_reference.file.filename, out alter_comp)) {
            Vala.Symbol? matching_sym;
            if ((matching_sym = SymbolReferences.find_matching_symbol (alter_comp.code_context, symbol)) != null)
                return matching_sym;
        }
        return symbol;
    }

    /**
     * Gets the range of a symbol name in a code node. For example, 
     * if we are replacing a method symbol, for each method call where that symbol
     * appears, we only want to replace the portion of the text that contains the 
     * symbol. This means we have to narrow the {@link Vala.SourceReference} of
     * the expression. This same problem exists for data types, where we may wish
     * to replace ``TypeName`` in every instance of ``Namespace.TypeName``.
     *
     * @param code_node             A code node in the AST. Its ``source_reference`` must be non-``null``.
     * @param symbol                The symbol to replace inside the code node.
     * @return                      The replacement range, or ``null`` if ``symbol.name`` is not inside it
     */
    Range? get_replacement_range (Vala.CodeNode code_node, Vala.Symbol symbol) {
        var range = new Range.from_sourceref (code_node.source_reference);

        string representation = CodeHelp.get_code_node_representation (code_node);
        int last_index_of_symbol = representation.last_index_of (symbol.name);

        if (last_index_of_symbol == -1)
            return null;
        
        // move the start of the range up [last_index_of_symbol] characters
        string prefix = representation[0:last_index_of_symbol];
        int last_index_of_newline_in_prefix = prefix.last_index_of_char ('\n');

        if (last_index_of_newline_in_prefix == -1) {
            range.start = range.start.translate (0, last_index_of_symbol);
        } else {
            int newline_count = 0;

            foreach (uint character in prefix.data)
                if ((char)character == '\n')
                    newline_count++;

            range.start = range.start.translate (newline_count, last_index_of_symbol - last_index_of_newline_in_prefix);
        }

        // move the end of the range back [length(symbol_name)] characters
        string suffix = representation[(last_index_of_symbol+symbol.name.length):representation.length];
        int last_index_of_newline_in_suffix = suffix.last_index_of_char ('\n');

        if (last_index_of_newline_in_suffix == -1) {
            range.end = range.end.translate (0, -(representation.length - (last_index_of_symbol + symbol.name.length)));
        } else {
            int newline_count = 0;

            foreach (uint character in suffix.data)
                if ((char)character == '\n')
                    newline_count++;
            
            range.end = range.end.translate (-newline_count, -(last_index_of_newline_in_suffix - (last_index_of_symbol + symbol.name.length)));
        }

        return range;
    }

    /**
     * List all references to @sym in @file
     *
     * @param file              the file to search for references in
     * @param sym               the symbol to search for references to
     * @param references        the collection to fill with references
     */
    void list_in_file (Vala.SourceFile file, Vala.Symbol sym, bool include_declaration, ArrayList<Vala.CodeNode> references) {
        var unique_srefs = new HashSet<string> ();
        if (sym is Vala.TypeSymbol) {
            var fs2 = new FindSymbol.with_filter (file, sym,
                (needle, node) => node == needle ||
                    (node is Vala.DataType && ((Vala.DataType) node).type_symbol == needle), include_declaration);
            foreach (var node in fs2.result) {
                if (!(node.source_reference.to_string () in unique_srefs)) {
                    references.add (node);
                    unique_srefs.add (node.source_reference.to_string ());
                }
            }
        }
        var fs2 = new FindSymbol.with_filter (file, sym, 
            (needle, node) => node == needle || 
                (node is Vala.Expression && ((Vala.Expression)node).symbol_reference == needle ||
                    node is Vala.UsingDirective && ((Vala.UsingDirective)node).namespace_symbol == needle), include_declaration);
        foreach (var node in fs2.result) {
            if (!(node.source_reference.to_string () in unique_srefs)) {
                references.add (node);
                unique_srefs.add (node.source_reference.to_string ());
            }
        }
    }

    /** 
     * It's possible that a symbol can be used across build targets within a
     * project. This returns a list of all pairs of ``(compilation, symbol)``
     * matching @sym where ``symbol`` is defined within ``compilation``.
     *
     * @param project       the project to search for a symbol in
     * @param symbol        the symbol to search for
     * @return              a list of pairs of ``(compilation, symbol)``
     */
    Collection<Pair<Compilation, Vala.Symbol>> get_compilations_using_symbol (Project project, Vala.Symbol symbol) {
        var compilations = new ArrayList<Pair<Compilation, Vala.Symbol>> ();

        foreach (var compilation in project.get_compilations ()) {
            Vala.Symbol? matching_sym = find_matching_symbol (compilation.code_context, symbol);
            if (matching_sym != null)
                compilations.add (new Pair<Compilation, Vala.Symbol> (compilation, matching_sym));
        }

        // find_matching_symbol() isn't reliable with local variables, especially those declared
        // in lambdas, which can change names after recompilation.
        if (symbol is Vala.LocalVariable) {
            project.get_compilations ()
                .filter (c => symbol.source_reference.file in c.code_context.get_source_files ())
                .foreach (compilation => {
                    compilations.add (new Pair<Compilation, Vala.Symbol> (compilation, symbol));
                    return false;
                });
        }

        return compilations;
    }
}