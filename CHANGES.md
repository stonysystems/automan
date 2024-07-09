# Syntax

- [X] add tuple types
- [X] add literals `true` and `false`
- [X] add attributes (can appear on functions, quantified variables, e.g. `{:trigger Q(x) }`)
- [X] add unary negation
- [X] add lambdas
- [X] generalize sequence displays (the form `seq(n, x => e)` generalizes to `seq(n,f)` where `f` is a function; `x => e` is a lambda expression)
- [X] add generic instantiations in terms
  but there is a potential ambiguity: e1 < e2 and e1 < tp >, since e2 and tp can be dot-suffixed identifiers with generic instantiations, too
- [X] better support for quantifier syntax
  attributes, collection domains and arbitrary ranges for quantified variables
- [X] better support for assert statements (assert EXPR by BLOCKSTMT)
- [X] restricting some `expr`s to `id` where appropriate (bound variables, member access, member update)
- [X] question (?) is part of an identifier, not an operator on expressions
