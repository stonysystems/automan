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
%token SET MAP SEQ INT BOOL NAT STR
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

%start file_level
%type <Syntax.ParserPass.FileLevel.t option> file_level
// %type <Syntax.ParserPass.Prog.t> expr

%%

/* expressions */
/* TODO: we need attributes to support lemma calls
   https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-top-level-expression
*/
expr:
  /* | e = equiv_expr { e } */
  | es = separated_nonempty_list(SEMI, equiv_expr)
    { Syntax.ParserPass.Prog.(
        Internal.NonEmptyList.fold_left_1
          (fun x y -> Lemma {lem = x; e = y})
          (Internal.NonEmptyList.coerce es))
    }

equiv_expr:
  | es = separated_nonempty_list(EQUIV, implies_explies_expr)
    { Syntax.ParserPass.Prog.(
        assoc_right_bop Equiv (Internal.NonEmptyList.coerce es))
    }

implies_explies_expr:
  | e = logic_expr; es = nonempty_list(implies_before_expr)
    { Syntax.ParserPass.Prog.(
        assoc_right_bop Implies (Internal.NonEmptyList.(e :: es)))
    }
  | e = logic_expr; es = nonempty_list(explies_before_expr)
    { Syntax.ParserPass.Prog.(
        assoc_right_bop
          Implies
          (Internal.NonEmptyList.coerce (List.rev (e :: es)))
      )}
  | e = logic_expr { e }

implies_before_expr: IMPLIES; e = logic_expr { e }

explies_before_expr: EXPLIES; e = logic_expr { e }

logic_expr:
  | es = nonempty_list(and_before_rel_expr)
    { Syntax.ParserPass.Prog.(
        assoc_right_bop And (Internal.NonEmptyList.coerce es))
    }
  | e = rel_expr; es = nonempty_list(and_before_rel_expr)
    { Syntax.ParserPass.Prog.(
        assoc_right_bop And (Internal.NonEmptyList.(::) (e, es)))
    }
  | es = nonempty_list(or_before_rel_expr)
    { Syntax.ParserPass.Prog.(
        assoc_right_bop Or (Internal.NonEmptyList.coerce es))
    }
  | e = rel_expr; es = nonempty_list(or_before_rel_expr)
    { Syntax.ParserPass.Prog.(
        assoc_right_bop Or (Internal.NonEmptyList.(::) (e, es)))
    }
  | e = rel_expr { e }

and_before_rel_expr: AND; e = rel_expr { e }

or_before_rel_expr: OR; e = rel_expr   { e }

/* BEGIN: relational operator symbols */
rel_op_lt_lte:
  | LTE    { Syntax.ParserPass.Prog.Lte }
  | LANGLE { Syntax.ParserPass.Prog.Lt }

rel_op_gt_gte:
  | GTE    { Syntax.ParserPass.Prog.Lte }
  | RANGLE { Syntax.ParserPass.Prog.Lt }

/* NOTE: In Dafny, NEQ is allowed to appear inside a chain of equalities. We
   don't support this (yet?)
*/
rel_op_nonchaining:
  | NEQ   { Syntax.ParserPass.Prog.Neq }
  | IN    { Syntax.ParserPass.Prog.In  }
  | NOTIN { Syntax.ParserPass.Prog.Nin }
/* END: relational operator symbols */

/* NOTE: use "shift_term" between rel_expr and term_expr
   if bitwise ops are to be added
*/
rel_expr:
  | e = rel_expr_chain_lte_lt { e }
  | e = rel_expr_chain_gte_gt { e }
  | e = rel_expr_chain_eq     { e }
  | e1 = term_expr;
    o  = rel_op_nonchaining;
    e2 = term_expr;           { Syntax.ParserPass.Prog.(Binary (o, e1, e2)) }
  | e = term_expr             { e }

rel_expr_chain_lte_lt:
  | e1 = term_expr; es = nonempty_list(o = rel_op_lt_lte; e = term_expr { (o, e) })
    { Syntax.ParserPass.Prog.chain_bop e1 es }

rel_expr_chain_gte_gt:
  | e1 = term_expr; es = nonempty_list(o = rel_op_gt_gte; e = term_expr { (o, e) })
    { Syntax.ParserPass.Prog.chain_bop e1 es }

rel_expr_chain_eq:
  | e1 = term_expr; es = nonempty_list(EQ; e = term_expr { (Syntax.ParserPass.Prog.Eq, e ) })
    { Syntax.ParserPass.Prog.chain_bop e1 es }

term_op:
  | ADD { Syntax.ParserPass.Prog.Add }
  | SUB { Syntax.ParserPass.Prog.Sub }

term_expr:
  |   e = factor_expr
    ; es = list(term_op_before_factor_expr)
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y ->
            let (top, y') = y in
            Binary (top, x, y'))
          e es)
    }

term_op_before_factor_expr: top = term_op; e2 = factor_expr { (top, e2) }

factor_op:
  | MULT { Syntax.ParserPass.Prog.Mul }
  | DIV  { Syntax.ParserPass.Prog.Div }
  | MOD  { Syntax.ParserPass.Prog.Mod }

factor_expr:
  |   e = unary_expr
    ; es = list(factor_op_before_expr)
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y ->
            let (top, y') = y in
            Binary (top, x, y'))
          e es)
    }

factor_op_before_expr: top = factor_op; e2 = unary_expr { (top, e2) }

unary_expr:
  | SUB; e = unary_expr
    { Syntax.ParserPass.Prog.(
        Unary (Neg, e))
    }
  | NOT; e = unary_expr
    { Syntax.ParserPass.Prog.(
        Unary (Not, e))}
  | e = primary_expr
    { e }

/* - primary expressions */
primary_expr:
  | e = name_seg; suffs = list(suffix)
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          e suffs)
    }
  | e = lambda_expr
    { e }
  | e = map_disp_expr; suffs = list(suffix)
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          e suffs)
    }
  | e = seq_disp_expr; suffs = list(suffix)
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          (SeqDisplay e) suffs)
    }
  | e = set_disp_expr; suffs = list(suffix)
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          e suffs)
    }
  | e = endless_expr
    { e }
  | e = constatom_expr; suffs = list(suffix)
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          e suffs)
    }

/* TODO: the usual problem with using <> for generic instantiation and < for
comparison */
name_seg:
  | x = ID /* ; tps = gen_inst */
    { Syntax.ParserPass.Prog.NameSeg (x, []) }

id_type_optional:
  | x = ID; COLON; tp = tp { (x, Some tp) }
  | x = ID                 { (x, None)    }

lambda_delimited_formals:
  | xs = delimited(LPAREN, separated_list(COMMA, id_type_optional), RPAREN) { xs }

lambda_formals:
  | x = ID                        { [(x, None)] }
  | xs = lambda_delimited_formals { xs }

/* NOTE: no lambda spec */
lambda_expr:
  | xs = lambda_formals; ARROW; bod = expr
    { Syntax.ParserPass.Prog.Lambda (xs, bod) }

seq_disp_expr:
  | LSQBRAC; es = separated_list(COMMA, expr); RSQBRAC
    { Syntax.ParserPass.Prog.SeqEnumerate es }
  | SEQ; tps = gen_inst; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN
    { Syntax.ParserPass.Prog.SeqTabulate { gen_inst = tps; len = e1; func = e2 }}

map_literal_expression:
  | e1 = expr; ASSIGN; e2 = expr { (e1, e2) }

map_disp_expr:
  |  MAP; es = delimited(LSQBRAC, separated_list(COMMA, map_literal_expression), RSQBRAC)
    { Syntax.ParserPass.Prog.MapDisplay es }

set_disp_expr:
  | LBRACE; es = separated_list(COMMA, expr); RBRACE
    { Syntax.ParserPass.Prog.SetDisplay es }

endless_expr:
  | IF; c = expr; THEN; t = expr; ELSE; e = expr
    { Syntax.ParserPass.Prog.If (c, t, e) }
  | e = match_expr
    { e }
  | e = quantifier_expr
    { e }
  | SET; qd = qvar_dom; e = option(QUANTIFY_SEP; e = expr { e })
    { Syntax.ParserPass.Prog.SetComp (qd, e) }
  /* let
     NOTE: no ghost, let-fail, assign-such-that */
  |   VAR
    ; pats = separated_nonempty_list(COMMA, case_pattern)
    ; ASSIGN
    ; vs = separated_nonempty_list(COMMA, equiv_expr)
    ; SEMI
    ; bod = expr
    { Syntax.ParserPass.Prog.(
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
    { Syntax.ParserPass.Prog.(
        match e2 with
        | None -> MapComp { qdom = qd; key = None; valu = e1}
        | Some e2 ->
           MapComp { qdom = qd; key = Some e1; valu = e2 }
        )
    }

case_pattern:
  | x = ID; tp = option(COLON; tp = tp { tp })
    { Syntax.ParserPass.Prog.PatVar (x, tp) }
  | x = option(ID); LPAREN; pats = separated_list(COMMA, case_pattern); RPAREN
    { Syntax.ParserPass.Prog.PatCtor (x, pats) }

extended_pattern:
  | l = lit
    { Syntax.ParserPass.Prog.EPatLit l }
  | x = ID; tp = option(COLON; tp = tp { tp })
    { Syntax.ParserPass.Prog.EPatVar (x, tp) }
  | x = option(ID); LPAREN; pats = separated_list(COMMA, extended_pattern); RPAREN
    { Syntax.ParserPass.Prog.EPatCtor (x, pats) }

case_expr:
  |   CASE
    ; attrs = list(attribute)
    ; pat = extended_pattern
    ; ARROW
    ; bod = expr
    { Syntax.ParserPass.Prog.Case (attrs, pat, bod) }

/* NOTE: we force case trees to have curly braces to avoid a shift/reduce conflict */
case_tree:
  | LBRACE; cases = list(case_expr); RBRACE
    { cases }
/*| cases = nonempty_list(case_expr) */
/*  { cases } */

match_expr:
  | MATCH; e = expr; tree = case_tree
    { Syntax.ParserPass.Prog.(
        Match (e, tree))
    }

quantifier:
  | FORALL { Syntax.ParserPass.Prog.Forall }
  | EXISTS { Syntax.ParserPass.Prog.Exists }

qvar_dom_coll: QVAR_DOM_COLL; e = expr { e }

qvar_dom_range: PIPE; e = expr { e }

qvar_decl:
  | xtp = id_type_optional; cdom = option(qvar_dom_coll); attrs = list(attribute)
    { let (x , tp) = xtp in Syntax.ParserPass.Prog.QVar (x, tp, cdom, attrs) }

qvar_dom:
  |   qvs = separated_nonempty_list(COMMA, qvar_decl)
    ; r = option(qvar_dom_range)
    { Syntax.ParserPass.Prog.QDom { qvars = qvs; qrange = r }}

quantifier_expr:
  | q = quantifier; qd = qvar_dom; QUANTIFY_SEP; e = expr
    { Syntax.ParserPass.Prog.Quantifier { qt = q; qdom = qd; qbody = e } }

constatom_expr:
  | e = lit
    { Syntax.ParserPass.Prog.Lit e }
  | THIS
    { Syntax.ParserPass.Prog.This }
  | e = delimited(PIPE, expr, PIPE)
    { Syntax.ParserPass.Prog.(Cardinality e)}
  | LPAREN; es = list(expr); RPAREN
    {
      Syntax.ParserPass.Prog.(
        match es with
        | [e] -> e
        | _   -> Tuple es
      )
    }

suffix:
  | s = dotsuffix; tps = gen_inst
    { Syntax.ParserPass.Prog.(
        AugDot (s, tps))
    }
  |   DOT
    ; LPAREN
    ; upds = separated_nonempty_list(COMMA, member_binding_upd)
    ; RPAREN
    { Syntax.ParserPass.Prog.(
        DataUpd (Internal.NonEmptyList.coerce upds))
    }
  | LSQBRAC; lb = option(expr); SLICE; ub = option(expr); RSQBRAC
    { Syntax.ParserPass.Prog.Subseq { lb = lb; ub = ub }}
  /* TODO: slices by length */
  | LSQBRAC; idx = expr; ASSIGN; valu = expr; RSQBRAC
    { Syntax.ParserPass.Prog.SeqUpd {idx = idx; v = valu }}
  | LSQBRAC; e = expr; RSQBRAC
    { Syntax.ParserPass.Prog.Sel e }
  | args = delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Syntax.ParserPass.Prog.ArgList args }

/* TODO: add requires, reads */
dotsuffix:
  | DOT; x = ID  { Syntax.DSId x }
  | DOT; n = NUM { Syntax.DSDig n }

member_binding_upd:
  | x = ID; ASSIGN; e = expr  { (Either.Left x, e) }
  | n = NUM; ASSIGN; e = expr { (Either.Right n, e) }

lit: /* TODO: character literals */
  | TRUE  { Syntax.ParserPass.Prog.True }
  | FALSE { Syntax.ParserPass.Prog.False}
  | NULL  { Syntax.ParserPass.Prog.Null }
  | x = STRING { Syntax.ParserPass.Prog.String x }
  | n = NUM    { Syntax.ParserPass.Prog.Nat n }

/* Types  */
tp_prim:
  | SET; LANGLE; t = tp; RANGLE
    { Syntax.ParserPass.Type.set t }
  | SEQ; LANGLE; t = tp; RANGLE
    { Syntax.ParserPass.Type.seq t }
  | MAP; LANGLE; t1 = tp; COMMA; t2 = tp; RANGLE
    { Syntax.ParserPass.Type.map t1 t2 }
  | INT
    { Syntax.ParserPass.Type.int }
  | BOOL
    { Syntax.ParserPass.Type.bool }
  | NAT
    { Syntax.ParserPass.Type.nat }
  | STR
    { Syntax.ParserPass.Type.bool }

tp_tup:
  | LPAREN; RPAREN { Syntax.ParserPass.Type.unit }
  | LPAREN; t1 = tp; COMMA; ts = nonempty_list(COMMA; t = tp { t })
    { Syntax.ParserPass.Type.TpTup (t1 :: ts) }

tp_name_seg:
  | x = ID; ts = gen_inst;
    { Syntax.ParserPass.Type.TpIdSeg { id = x; gen_inst = ts }}

tp:
  | t = tp_prim { t }
  | t = tp_tup  { t }
  | nss = separated_nonempty_list(DOT, tp_name_seg)
    { Syntax.ParserPass.Type.TpName (Internal.NonEmptyList.coerce nss) }

gen_inst:
  | tps = delimited(LANGLE, separated_nonempty_list(COMMA, tp), RANGLE) { tps }
  | /* empty */
    { [] }

/* misc */
attribute:
  | LBRACECOLON; a = ID; args = separated_list(COMMA, expr); RBRACE
    { (a, args) }

/* module declarations */
formal:
  | x = ID; COLON; t = tp
    { Syntax.ParserPass.ModuleItem.Formal (x, t) }

/* TODO: parallel pipes for constructors? (like &&, ||) */
datatype_ctor:
  | c = ID; LPAREN; fs = separated_list(COMMA, formal); RPAREN
    { Syntax.ParserPass.ModuleItem.DatatypeCtor (c, fs) }

datatype_ctors:
  | cs = separated_list(PIPE, datatype_ctor) { cs }

function_spec:
  | REQUIRES; e = expr
    { Syntax.ParserPass.ModuleItem.Requires e }
  /* | READS; e = expr */
  /*   { Syntax.ParserPass.ModuleItem.Reads e } */
  | ENSURES; e = expr
    { Syntax.ParserPass.ModuleItem.Ensures e }
  | DECREASES; e = expr
    { Syntax.ParserPass.ModuleItem.Decreases e }


module_item:
  | IMPORT; OPENED; m = ID
    { Syntax.ParserPass.ModuleItem.Import m }
  | DATATYPE; d = ID; SGEQ; cs = datatype_ctors;
    { Syntax.ParserPass.ModuleItem.DatatypeDef (d, cs) }
  | PREDICATE; p = ID;
    fs = delimited(LPAREN, separated_list(COMMA, formal), RPAREN);
    specs = list(function_spec);
    e = delimited(LBRACE, expr, RBRACE);
    { Syntax.ParserPass.ModuleItem.Predicate (p, fs, specs, e) }

  | TYPE; n = ID; SGEQ; t = tp
    { Syntax.ParserPass.ModuleItem.Alias (n, t) }

/* file-level directives */
file_level:
  | INCLUDE; fp = STRING
    { Some (Syntax.ParserPass.FileLevel.Include fp) }
  | MODULE; m = ID; LBRACE; ds = list(module_item); RBRACE
    { Some (Syntax.ParserPass.FileLevel.Module (m, ds)) }
  | EOF
    { None }
