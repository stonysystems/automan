/* Lexemes */

%token INCLUDE
%token IMPORT
%token OPENED
%token DATATYPE
%token MODULE
%token PREDICATE
%token FORALL
%token EXISTS
%token VAR
%token REQUIRES ENSURES DECREASES
%token ASSERT
%token FUNCTION
%token LEMMA
%token TYPE
%token THIS

%token SLICE
%token ASSIGN
%token IF THEN ELSE MATCH CASE
%token SET MAP SEQ
%token ADD SUB MULT DIV MOD

%token AND OR
%token EQ NEQ LTE GTE IN NOTIN

%token TRUE FALSE NULL
%token <string> STRING
%token <string> ID
%token <int>    NUM

%token LBRACE LBRACECOLON RBRACE
%token LPAREN  RPAREN
%token LANGLE  RANGLE
%token LSQBRAC RSQBRAC

%token IMPLIES
%token EXPLIES
%token EQUIV
%token QUANTIFY_SEP
%token QVAR_DOM_COLL ARROW

%token COLON
%token COMMA
%token PIPE
%token SEMI

%token SGEQ
%token NOT
%token DOT
%token EOF

%left  QUANTIFY_SEP
%right IMPLIES EQUIV
%left  EXPLIES

%left  SEMI
%left  ELSE

%left  PIPE

%left  AND OR
%left  EQ NEQ LTE GTE IN NOTIN

%left  LSQBRAC

%left  LBRACE
%left  LANGLE
%left  RANGLE

%left  ADD  SUB
%left  MULT DIV
%left  MOD

%left  SLICE

%left  NOT
%left  DOT

%start expr
// %type <Syntax.ParserPass.file_level option> file
%type <Syntax.ParserPass.Expr.t> expr

%%

/* expressions */
expr:
  | es = separated_nonempty_list(SEMI, equiv_expr)
    { Syntax.ParserPass.Expr.(
        foldr1 (fun x y -> Lemma {lem = x; e = y}) es)
    }

equiv_expr:
  | es = separated_nonempty_list(EQUIV, implies_explies_expr)
    { Syntax.ParserPass.Expr.(
        foldr1 (fun x y -> Binary (Equiv, x, y))) es
    }

implies_explies_expr:
  | e = logic_expr; es = nonempty_list(IMPLIES; e = logic_expr { e })
    { Syntax.ParserPass.Expr.(
        foldr1 (fun x y -> Binary (Implies, x, y)) (e :: es))
    }
  | e = logic_expr; es = nonempty_list(EXPLIES; e = logic_expr { e })
    { Syntax.ParserPass.Expr.(
        foldl1 (fun x y -> Binary (Implies, y, x)) (e :: es)
      )}
  | e = logic_expr { e }

logic_expr:
  | es = nonempty_list(AND; e = rel_expr { e })
    { Syntax.ParserPass.Expr.(
        foldr1 (fun x y -> Binary (And, x, y)) es)
    }
  | e = rel_expr; es = nonempty_list(AND; e = rel_expr { e })
    { Syntax.ParserPass.Expr.(
        foldr1 (fun x y -> Binary (And, x, y)) (e :: es))
    }
  | es = nonempty_list(OR; e = rel_expr { e })
    { Syntax.ParserPass.Expr.(
        foldr1 (fun x y -> Binary (Or, x, y)) es)
    }
  | e = rel_expr; es = nonempty_list(OR; e = rel_expr { e })
    { Syntax.ParserPass.Expr.(
        foldr1 (fun x y -> Binary (Or, x, y)) (e :: es))
    }
  | e = rel_expr { e }

rel_op:
  | EQ     { Syntax.ParserPass.Expr.Eq }
  | NEQ    { Syntax.ParserPass.Expr.Eq }
  | LTE    { Syntax.ParserPass.Expr.Lte }
  | GTE    { Syntax.ParserPass.Expr.Gte }
  | LANGLE { Syntax.ParserPass.Expr.Lt }
  | RANGLE { Syntax.ParserPass.Expr.Gt }

/* NOTE: chaining not supported!
   NOTE: use "shift_term" between rel_expr and term_expr
         if bitwise ops are to be added
*/
rel_expr:
  | e1 = term_expr; rop = rel_op; e2 = term_expr
    { Syntax.ParserPass.Expr.(
        Binary (rop, e1, e2))
    }

term_op:
  | ADD { Syntax.ParserPass.Expr.Add }
  | SUB { Syntax.ParserPass.Expr.Sub }

term_expr:
  |   e = factor_expr
    ; es = list(top = term_op; e2 = factor_expr { (top, e2) })
    { Syntax.ParserPass.Expr.(
        List.fold_left
          (fun x y ->
            let (top, y') = y in
            Binary (top, x, y'))
          e es)
    }

factor_op:
  | MULT { Syntax.ParserPass.Expr.Mul }
  | DIV  { Syntax.ParserPass.Expr.Div }
  | MOD  { Syntax.ParserPass.Expr.Mod }

factor_expr:
  |   e = unary_expr
    ; es = list(top = factor_op; e2 = unary_expr { (top, e2) })
    { Syntax.ParserPass.Expr.(
        List.fold_left
          (fun x y ->
            let (top, y') = y in
            Binary (top, x, y'))
          e es)
    }

unary_expr:
  | SUB; e = unary_expr
    { Syntax.ParserPass.Expr.(
        Unary (Neg, e))
    }
  | NOT; e = unary_expr
    { Syntax.ParserPass.Expr.(
        Unary (Not, e))}
  | e = primary_expr
    { e }

/* - primary expressions */
primary_expr:
  | e = name_seg; suffs = list(suffix)
    { Syntax.ParserPass.Expr.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          e suffs)
    }
  | e = lambda_expr
    { e }
  | e = map_disp_expr; suffs = list(suffix)
    { Syntax.ParserPass.Expr.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          e suffs)
    }
  | e = seq_disp_expr; suffs = list(suffix)
    { Syntax.ParserPass.Expr.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          (SeqDisplay e) suffs)
    }
  | e = set_disp_expr; suffs = list(suffix)
    { Syntax.ParserPass.Expr.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          e suffs)
    }
  | e = endless_expr
    { e }
  | e = constatom_expr; suffs = list(suffix)
    { Syntax.ParserPass.Expr.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          e suffs)
    }

name_seg:
  | x = ID; tps = gen_inst { Syntax.ParserPass.Expr.NameSeg (x, tps) }

lambda_formals:
  | x = ID { [(x, None)] }
  |   LPAREN
    ; xs = separated_nonempty_list
        (COMMA
        , x = ID; tp = option(COLON; tp = tp { tp }) { (x, tp) })
    ; RPAREN
    { xs }

/* NOTE: no lambda spec */
lambda_expr:
  | xs = lambda_formals; ARROW; bod = expr
    { Syntax.ParserPass.Expr.Lambda (xs, bod) }

seq_disp_expr:
  | LSQBRAC; es = separated_list(COMMA, expr); RSQBRAC
    { Syntax.ParserPass.Expr.SeqEnumerate es }
  | SEQ; tps = gen_inst; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN
    { Syntax.ParserPass.Expr.SeqTabulate { gen_inst = tps; len = e1; func = e2 }}

map_disp_expr:
  |   MAP
    ; LSQBRAC
    ; es = separated_nonempty_list
      (COMMA
      , e1 = expr; ASSIGN; e2 = expr
        { (e1, e2) })
    { Syntax.ParserPass.Expr.MapDisplay es }

set_disp_expr:
  | LBRACE; es = separated_list(COMMA, expr); RBRACE
    { Syntax.ParserPass.Expr.SetDisplay es }

endless_expr:
  | IF; c = expr; THEN; t = expr; ELSE; e = expr
    { Syntax.ParserPass.Expr.If (c, t, e) }
  | e = match_expr
    { e }
  | e = quantifier_expr
    { e }
  | SET; qd = qvar_dom; e = option(QUANTIFY_SEP; e = expr { e })
    { Syntax.ParserPass.Expr.SetComp (qd, e) }
  /* let
     NOTE: no ghost, let-fail, assign-such-that */
  |   VAR
    ; pats = separated_nonempty_list(COMMA, case_pattern)
    ; ASSIGN
    ; vs = separated_nonempty_list(COMMA, equiv_expr)
    ; SEMI
    ; bod = expr
    { Syntax.ParserPass.Expr.(
        Let
          { ghost = false
          ; pats = Internal.NonEmptyList.coerce pats
          ; def  = Internal.NonEmptyList.coerce vs
          ; body = bod})
    }
  |   MAP
    ; qd = qvar_dom
    ; QUANTIFY_SEP
    ; e1 = expr
    ; e2 = option(ASSIGN; e = expr { e })
    { Syntax.ParserPass.Expr.(
        match e2 with
        | None -> MapComp { qdom = qd; key = None; valu = e1}
        | Some e2 ->
           MapComp { qdom = qd; key = Some e1; valu = e2 }
        )
    }

case_pattern:
  | x = ID; tp = option(COLON; tp = tp { tp })
    { Syntax.ParserPass.Expr.PatVar (x, tp) }
  | x = option(ID); LPAREN; pats = separated_list(COMMA, case_pattern); RPAREN
    { Syntax.ParserPass.Expr.PatCtor (x, pats) }

extended_pattern:
  | l = lit
    { Syntax.ParserPass.Expr.EPatLit l }
  | x = ID; tp = option(COLON; tp = tp { tp })
    { Syntax.ParserPass.Expr.EPatVar (x, tp) }
  | x = option(ID); LPAREN; pats = separated_list(COMMA, extended_pattern); RPAREN
    { Syntax.ParserPass.Expr.EPatCtor (x, pats) }

case_expr:
  |   CASE
    ; attrs = list(attribute)
    ; pat = extended_pattern
    ; ARROW
    ; bod = expr
    { Syntax.ParserPass.Expr.Case (attrs, pat, bod) }

/* NOTE: we force case trees to have curly braces to avoid a shift/reduce conflict */
case_tree:
  | LBRACE; cases = list(case_expr); RBRACE
    { cases }
/*| cases = nonempty_list(case_expr) */
/*  { cases } */

match_expr:
  | MATCH; e = expr; tree = case_tree
    { Syntax.ParserPass.Expr.(
        Match (e, tree))
    }

quantifier:
  | FORALL { Syntax.ParserPass.Expr.Forall }
  | EXISTS { Syntax.ParserPass.Expr.Exists }

qvar_decl:
  |   x = ID
    ; typ = option(COLON; typ = tp { typ })
    ; cdom = option(QVAR_DOM_COLL; e = expr { e })
    ; attrs = list(attribute)
    { Syntax.ParserPass.Expr.QVar (x, typ, cdom, attrs) }

qvar_dom:
  |   qvs = separated_nonempty_list(COMMA, qvar_decl)
    ; r = option(PIPE; e = expr { e })
    { Syntax.ParserPass.Expr.QDom { qvars = qvs; qrange = r }}

quantifier_expr:
  | q = quantifier; qd = qvar_dom; QUANTIFY_SEP; e = expr
    { Syntax.ParserPass.Expr.Quantifier { qt = q; qdom = qd; qbody = e } }

constatom_expr:
  | e = lit
    { Syntax.ParserPass.Expr.Lit e }
  | THIS
    { Syntax.ParserPass.Expr.This }
  | PIPE; e = expr; PIPE
    { Syntax.ParserPass.Expr.(Cardinality e)}
  | LPAREN; es = list(expr); RPAREN
    {
      Syntax.ParserPass.Expr.(
        match es with
        | [e] -> e
        | _   -> Tuple es
      )
    }

suffix:
  | s = dotsuffix; tps = gen_inst
    { Syntax.ParserPass.Expr.(
        AugDot (s, tps))
    }
  |   DOT
    ; LPAREN
    ; upds = separated_nonempty_list(COMMA, member_binding_upd)
    ; RPAREN
    { Syntax.ParserPass.Expr.(
        DataUpd (Internal.NonEmptyList.coerce upds))
    }
  | LSQBRAC; lb = option(expr); SLICE; ub = option(expr); RSQBRAC
    { Syntax.ParserPass.Expr.Subseq { lb = lb; ub = ub }}
  /* TODO: slices by length */
  | LSQBRAC; idx = expr; ASSIGN; valu = expr; RSQBRAC
    { Syntax.ParserPass.Expr.SeqUpd {idx = idx; v = valu }}
  | LSQBRAC; e = expr; RSQBRAC
    { Syntax.ParserPass.Expr.Sel e }
  | LPAREN; args = separated_list(COMMA, expr); RPAREN
    { Syntax.ParserPass.Expr.ArgList args }

/* TODO: add requires, reads */
dotsuffix:
  | x = ID  { Syntax.DSId x }
  | n = NUM { Syntax.DSDig n }

member_binding_upd:
  | x = ID; ASSIGN; e = expr  { (Either.Left x, e) }
  | n = NUM; ASSIGN; e = expr { (Either.Right n, e) }

lit: /* TODO: character literals */
  | TRUE  { Syntax.ParserPass.Expr.True }
  | FALSE { Syntax.ParserPass.Expr.False}
  | NULL  { Syntax.ParserPass.Expr.Null }
  | x = STRING { Syntax.ParserPass.Expr.String x }

/* Types  */
tp_id:
  | SET     { "set" }
  | MAP     { "map" }
  | SEQ     { "seq" }
  | x = ID  { x     }

tp:
  | LPAREN; es = separated_nonempty_list(COMMA, tp); RPAREN
    { Syntax.ParserPass.Type.(
        TpTup es)
    }
  | ns = separated_nonempty_list
      (DOT
      ,   x = tp_id
        ; tps = gen_inst
          { Syntax.ParserPass.Type.TpIdSeg { id = x; gen_inst = tps } })
    { Syntax.ParserPass.Type.TpName (Internal.NonEmptyList.coerce ns) }

gen_inst:
  | LANGLE; tps = separated_nonempty_list(COMMA, tp); RANGLE
    { tps }
  | /* empty */
    { [] }

/* misc */
attribute:
  | LBRACECOLON; a = ID; args = separated_list(COMMA, expr); RBRACE
    { (a, args) }

/*
  | e1 = logic_expr; IMPLIES; e2 = implies_expr
    { Syntax.ParserPass.Expr.(
        Binary (Implies, e1, e2))
    }
  | e1 = logic_expr; es = separated_nonempty_list(EXPLILES, logic_expr)
    { Syntax.ParserPass.Expr.(
        foldr1 (fun x y -> Binary (Implies, y, x)) (e1 :: es))
    }
  | e = logic_expr
    { e }
*/
