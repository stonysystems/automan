%start toplevel
%type <Syntax.Annotation.toplevel_t> toplevel

%%

mode:
  | ADD { Syntax.Annotation.Input  }
  | SUB { Syntax.Annotation.Output }

item:
  | MODULE; n = ID; xs = delimited(LBRACE, list(item), RBRACE)
    { Syntax.Annotation.Module (n, xs) }
  | n = ID; xs = delimited(LPAREN, separated_list(COMMA, mode), RPAREN); SEMI
    { Syntax.Annotation.Function (n, xs) }

toplevel:
  | xs = list(item); EOF { xs }
