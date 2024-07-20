%start toplevel
%type <Syntax.AutoMan.toplevel_t> toplevel

%%

mode:
  | ADD { Syntax.AutoMan.Input  }
  | SUB { Syntax.AutoMan.Output }

item:
  | MODULE; n = ID; xs = delimited(LBRACE, list(item), RBRACE)
    { Syntax.AutoMan.Module (n, xs) }
  | n = ID; xs = delimited(LPAREN, separated_list(COMMA, mode), RPAREN); SEMI
    { Syntax.AutoMan.Function (n, xs) }

toplevel:
  | xs = list(item); EOF { xs }
