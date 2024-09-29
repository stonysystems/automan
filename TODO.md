# Parser/Lexer

- [ ] Arrow types (`S --> T`) are not supported.

- [ ] The lexer currently does not track character position for line comments,
      which means the line numbers in the reported locations of syntax errors
      are off by the number of lines beginning with // (ignoring whitespace).
      Ideally, these character positions would be tracked.

- [ ] lib/parser.mly needs to be modified to use attributes in the grammar
      productions (indicating e.g. where lemma calls and lambda expressions can
      appear in expressions) in order to resolve some conflicts

- [ ] the ambiguiting in generic instantiations (A < B > vs A < B) may not be
      parsable by an LR(1) grammar (it isn't in Java or C++, and Rust skirts the
      issue with the turbofish operator). Worst-case scenario means manually
      handling parse errors and performing backtracking.

- [ ] current parser has a number of shift/reduce and 2 reduce/reduce conflicts.
      The two items above are big contributers, but may not be the only source
      of the conflicts

- [ ] Match expressions require curly braces around the case tree.

- [ ] lambda expressions can only be of the form ID => EXPR (there is a parser
      conflict with parenthesized formal parameters and tuples)

- [ ] Several sorts of statements are not currently parsed (reveal, TODO list
      here)

- [ ] `ghost` modifier is not currently parsed

- [X] Language support for named parameters in argument lists

# Annotator

## Nice-to-haves
- [ ] annotation files should ideally be searched while processing Dafny
      `include` directives, not presented all upfront as is done currently
- [ ] following on the previous item, for harmony and saturation, as well as
      type user-provided annotations for type indirection, its desirable to
      chase down includes to know type / datatpe definitions (to know what their
      fields are).

- [ ] users may want to introduce some indirection to certain types

- [ ] Some kind of state relationship would be useful for giving default
      implementations for partial specifications.

