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
    { Syntax.Annotation.Predicate (n, xs) }

  | TYPE; n = ID; SGEQ; tp = tp; SEMI
    { Syntax.Annotation.TypeAlias (n, tp) }

toplevel:
  | xs = list(item); EOF { xs }

/* Types (TODO: copied from `dafnyParser.mly`, investigate sharing)  */
tp_prim:
  | SET; LANGLE; t = tp; RANGLE
    { Syntax.ParserPass.Type.set t () }
  | SEQ; LANGLE; t = tp; RANGLE
    { Syntax.ParserPass.Type.seq t () }
  | MAP; LANGLE; t1 = tp; COMMA; t2 = tp; RANGLE
    { Syntax.ParserPass.Type.map t1 t2 () }
  | INT
    { Syntax.ParserPass.Type.int () }
  | BOOL
    { Syntax.ParserPass.Type.bool () }
  | NAT
    { Syntax.ParserPass.Type.nat () }
  | STR
    { Syntax.ParserPass.Type.bool () }

tp_tup:
  | tps = delimited(LPAREN, separated_nonempty_list(COMMA, tp), RPAREN)
    { Syntax.ParserPass.Type.tuple tps }

tp_name_seg:
  | x = ID; ts = gen_inst;
    { Syntax.ParserPass.Type.TpIdSeg { id = x; gen_inst = ts }}

tp:
  | t = tp_prim { t }
  | t = tp_tup  { t }
  | nss = separated_nonempty_list(DOT, tp_name_seg)
    { Syntax.ParserPass.Type.TpName (Internal.NonEmptyList.coerce nss, ()) }

gen_inst:
  | tps = delimited(LANGLE, separated_nonempty_list(COMMA, tp), RANGLE) { tps }
  | /* empty */
    { [] }

