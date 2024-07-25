
%start dafny
/* NOTE: OCaml gets confused and fully qualifies the type name generic_params_t,
   which makes Dune think there is a circular dependency
*/
%type <Syntax.ParserPass.Type.generic_params_t> gen_params
%type <Syntax.ParserPass.TopDecl.t> top_decl
%type <Syntax.ParserPass.t> dafny
%type <Syntax.ParserPass.Prog.var_decl_id_lhs_t> stmt_vardecl_lhs
// %type <Syntax.ParserPass.Prog.t> expr

%%

/* expressions */
/* TODO: we need attributes to support lemma calls
   https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-top-level-expression
*/
yeslem: SEMI {()}

expr(LEM):
  | es = separated_nonempty_list(LEM, equiv_expr(NOLEM)) /* Passing `LEM` introduces ~40 shift/reduce conflicts... */
    { Syntax.ParserPass.Prog.(
        Internal.NonEmptyList.fold_right_1
          (fun x y -> Lemma { lem = x; e = y })
          (Internal.NonEmptyList.coerce es)
    )}

equiv_expr(LEM):
  | es = separated_nonempty_list(EQUIV, implies_explies_expr(LEM))
    { Syntax.ParserPass.Prog.(
        assoc_right_bop Equiv (Internal.NonEmptyList.coerce es))
    }

implies_explies_expr(LEM):
  | e = logic_expr(LEM); es = nonempty_list(implies_before_expr(LEM))
    { Syntax.ParserPass.Prog.(
        assoc_right_bop Implies (Internal.NonEmptyList.(e :: es)))
    }
  | e = logic_expr(LEM); es = nonempty_list(explies_before_expr(LEM))
    { Syntax.ParserPass.Prog.(
        assoc_right_bop
          Implies
          (Internal.NonEmptyList.coerce (List.rev (e :: es)))
      )}
  | e = logic_expr(LEM) { e }

implies_before_expr(LEM): IMPLIES; e = logic_expr(LEM) { e }

explies_before_expr(LEM): EXPLIES; e = logic_expr(LEM) { e }

logic_expr(LEM):
  | es = nonempty_list(and_before_rel_expr(LEM))
    { Syntax.ParserPass.Prog.(
        assoc_right_bop And (Internal.NonEmptyList.coerce es))
    }
  | e = rel_expr(LEM); es = nonempty_list(and_before_rel_expr(LEM))
    { Syntax.ParserPass.Prog.(
        assoc_right_bop And (Internal.NonEmptyList.(::) (e, es)))
    }
  | es = nonempty_list(or_before_rel_expr(LEM))
    { Syntax.ParserPass.Prog.(
        assoc_right_bop Or (Internal.NonEmptyList.coerce es))
    }
  | e = rel_expr(LEM); es = nonempty_list(or_before_rel_expr(LEM))
    { Syntax.ParserPass.Prog.(
        assoc_right_bop Or (Internal.NonEmptyList.(::) (e, es)))
    }
  | e = rel_expr(LEM) { e }

and_before_rel_expr(LEM): AND; e = rel_expr(LEM) { e }

or_before_rel_expr(LEM): OR; e = rel_expr(LEM)   { e }

/* BEGIN: relational operator symbols */
rel_op_lt_lte:
  | LTE    { Syntax.Common.Lte }
  | LANGLE { Syntax.Common.Lt }

rel_op_gt_gte:
  | GTE    { Syntax.Common.Lte }
  | RANGLE { Syntax.Common.Lt }

/* NOTE: In Dafny, NEQ is allowed to appear inside a chain of equalities. We
   don't support this (yet?)
*/
rel_op_nonchaining:
  | NEQ   { Syntax.Common.Neq }
  | IN    { Syntax.Common.In  }
  | NOTIN { Syntax.Common.Nin }
/* END: relational operator symbols */

/* NOTE: use "shift_term" between rel_expr and term_expr
   if bitwise ops are to be added
*/
rel_expr(LEM):
  | e = rel_expr_chain_lte_lt(LEM) { e }
  | e = rel_expr_chain_gte_gt(LEM) { e }
  | e = rel_expr_chain_eq(LEM)     { e }
  | e1 = term_expr(LEM);
    o  = rel_op_nonchaining;
    e2 = term_expr(LEM);           { Syntax.ParserPass.Prog.(Binary (o, e1, e2)) }
  | e = term_expr(LEM)             { e }

rel_expr_chain_lte_lt(LEM):
  | e1 = term_expr(LEM); es = nonempty_list(o = rel_op_lt_lte; e = term_expr(LEM) { (o, e) })
    { Syntax.ParserPass.Prog.chain_bop e1 es }

rel_expr_chain_gte_gt(LEM):
  | e1 = term_expr(LEM); es = nonempty_list(o = rel_op_gt_gte; e = term_expr(LEM) { (o, e) })
    { Syntax.ParserPass.Prog.chain_bop e1 es }

rel_expr_chain_eq(LEM):
  | e1 = term_expr(LEM);
    es = nonempty_list(EQ; e = term_expr(LEM) { (Syntax.Common.Eq, e) })
    { Syntax.ParserPass.Prog.chain_bop e1 es }

term_op:
  | ADD { Syntax.Common.Add }
  | SUB { Syntax.Common.Sub }

term_expr(LEM):
  |   e = factor_expr(LEM)
    ; es = list(term_op_before_factor_expr(LEM))
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y ->
            let (top, y') = y in
            Binary (top, x, y'))
          e es)
    }

term_op_before_factor_expr(LEM): top = term_op; e2 = factor_expr(LEM) { (top, e2) }

factor_op:
  | MULT { Syntax.Common.Mul }
  | DIV  { Syntax.Common.Div }
  | MOD  { Syntax.Common.Mod }

factor_expr(LEM):
  |   e = unary_expr(LEM)
    ; es = list(factor_op_before_expr(LEM))
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y ->
            let (top, y') = y in
            Binary (top, x, y'))
          e es)
    }

factor_op_before_expr(LEM): top = factor_op; e2 = unary_expr(LEM) { (top, e2) }

unary_expr(LEM):
  | SUB; e = unary_expr(LEM)
    { Syntax.ParserPass.Prog.(
        Unary (Neg, e))
    }
  | NOT; e = unary_expr(LEM)
    { Syntax.ParserPass.Prog.(
        Unary (Not, e))}
  | e = primary_expr(LEM)
    { e }

/* - primary expressions */
primary_expr(LEM):
  | e = name_seg; suffs = list(suffix)
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          e suffs)
    }
  | e = lambda_expr(LEM)
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
  | e = endless_expr(LEM)
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
lambda_expr(LEM):
  | xs = lambda_formals; ARROW; bod = expr(LEM)
    { Syntax.ParserPass.Prog.Lambda (xs, bod) }

seq_disp_expr:
  | LSQBRAC; es = separated_list(COMMA, expr(yeslem)); RSQBRAC
    { Syntax.ParserPass.Prog.SeqEnumerate es }
  | SEQ; tps = gen_inst; LPAREN; e1 = expr(yeslem); COMMA; e2 = expr(yeslem); RPAREN
    { Syntax.ParserPass.Prog.SeqTabulate { gen_inst = tps; len = e1; func = e2 }}

map_literal_expression:
  | e1 = expr(yeslem); ASSIGN; e2 = expr(yeslem) { (e1, e2) }

map_disp_expr:
  |  MAP; es = delimited(LSQBRAC, separated_list(COMMA, map_literal_expression), RSQBRAC)
    { Syntax.ParserPass.Prog.MapDisplay es }

set_disp_expr:
  | LBRACE; es = separated_list(COMMA, expr(yeslem)); RBRACE
    { Syntax.ParserPass.Prog.SetDisplay es }

/* TODO: StmtInExpr */
endless_expr(LEM):
  | IF; c = expr(yeslem); THEN; t = expr(yeslem); ELSE; e = expr(LEM)
    { Syntax.ParserPass.Prog.If (c, t, e) }
  | e = match_expr(LEM)
    { e }
  | e = quantifier_expr(LEM)
    { e }
  | SET; qd = qvar_dom(LEM); e = option(QUANTIFY_SEP; e = expr(yeslem) { e })
    { Syntax.ParserPass.Prog.SetComp (qd, e) }
  /* let
     NOTE: no ghost, let-fail, assign-such-that */
  | e = let_expr(LEM) { e }
  |   MAP
    ; qd = qvar_dom(LEM)
    ; QUANTIFY_SEP
    ; e1 = expr(LEM)
    ; e2 = option(ASSIGN; e = expr(LEM) { e })
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
  | x = option(ID); pats = delimited(LPAREN, separated_list(COMMA, case_pattern), RPAREN);
    { Syntax.ParserPass.Prog.PatCtor (x, pats) }

extended_pattern:
  | l = lit
    { Syntax.ParserPass.Prog.EPatLit l }
  | x = ID; tp = option(COLON; tp = tp { tp })
    { Syntax.ParserPass.Prog.EPatVar (x, tp) }
  | x = option(ID); LPAREN; pats = separated_list(COMMA, extended_pattern); RPAREN
    { Syntax.ParserPass.Prog.EPatCtor (x, pats) }

case_expr: /* (LEM) needed to support curly-less matches */
  |   CASE
    ; attrs = list(attribute)
    ; pat = extended_pattern
    ; ARROW
    ; bod = expr(yeslem)
    { Syntax.ParserPass.Prog.Case (attrs, pat, bod) }

/* NOTE: we force case trees to have curly braces to avoid a shift/reduce conflict */
case_tree:
  | cases = delimited(LBRACE, list(case_expr), RBRACE)
    { cases }
/*| cases = nonempty_list(case_expr) */
/*  { cases } */

match_expr(LEM):
  | MATCH; e = expr(LEM); tree = case_tree /* (LEM) needed if curly-less matches supported */
    { Syntax.ParserPass.Prog.(
        Match (e, tree))
    }

quantifier:
  | FORALL { Syntax.Common.Forall }
  | EXISTS { Syntax.Common.Exists }

qvar_dom_coll(LEM): QVAR_DOM_COLL; e = expr(LEM) { e }

qvar_dom_range(LEM): PIPE; e = expr(LEM) { e }

qvar_decl(LEM):
  | xtp = id_type_optional; cdom = option(qvar_dom_coll(LEM)); attrs = list(attribute)
    { let (x , tp) = xtp in Syntax.ParserPass.Prog.QVar (x, tp, cdom, attrs) }

qvar_dom(LEM):
  |   qvs = separated_nonempty_list(COMMA, qvar_decl(LEM))
    ; r = option(qvar_dom_range(LEM))
    { Syntax.ParserPass.Prog.QDom { qvars = qvs; qrange = r }}

quantifier_expr(LEM):
  | q = quantifier; qd = qvar_dom(LEM); QUANTIFY_SEP; e = expr(LEM)
    { Syntax.ParserPass.Prog.Quantifier { qt = q; qdom = qd; qbody = e } }

let_expr(LEM):
    | VAR
    ; pats = separated_nonempty_list(COMMA, case_pattern)
    ; ASSIGN
    ; vs = separated_nonempty_list(COMMA, expr(NOLEM))
    ; SEMI
    ; bod = expr(LEM)
    { Syntax.ParserPass.Prog.(
        Let
          { ghost = false
          ; pats = Internal.NonEmptyList.coerce pats
          ; defs = Internal.NonEmptyList.coerce vs
          ; body = bod})
    }


constatom_expr:
  | e = lit
    { Syntax.ParserPass.Prog.Lit e }
  | THIS
    { Syntax.ParserPass.Prog.This }
  | e = delimited(PIPE, expr(yeslem), PIPE)
    { Syntax.ParserPass.Prog.(Cardinality e)}
  | LPAREN; es = list(expr(yeslem)); RPAREN
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
  | LSQBRAC; lb = option(expr(yeslem)); SLICE; ub = option(expr(yeslem)); RSQBRAC
    { Syntax.ParserPass.Prog.Subseq { lb = lb; ub = ub }}
  /* TODO: slices by length */
  | LSQBRAC; idx = expr(yeslem); ASSIGN; valu = expr(yeslem); RSQBRAC
    { Syntax.ParserPass.Prog.SeqUpd {idx = idx; v = valu }}
  | LSQBRAC; e = expr(yeslem); RSQBRAC
    { Syntax.ParserPass.Prog.Sel e }
  | s = call_suffix
    { s }

/* TODO: add requires, reads */
dotsuffix:
  | DOT; x = ID  { Syntax.Common.DSId x }
  | DOT; n = NUM { Syntax.Common.DSDig n }

member_binding_upd:
  | x = ID; ASSIGN; e = expr(yeslem)  { (Either.Left x, e) }
  | n = NUM; ASSIGN; e = expr(yeslem) { (Either.Right n, e) }

call_suffix:
  | args = delimited(LPAREN, separated_list(COMMA, expr(yeslem)), RPAREN)
    { Syntax.ParserPass.Prog.ArgList args }

lit: /* TODO: character literals */
  | TRUE  { Syntax.Common.True }
  | FALSE { Syntax.Common.False}
  | NULL  { Syntax.Common.Null }
  | x = STRING { Syntax.Common.String x }
  | n = NUM    { Syntax.Common.Nat n }

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
  | tps = delimited(LPAREN, separated_nonempty_list(COMMA, tp), RPAREN)
    { Syntax.ParserPass.Type.tuple tps }

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

gen_params:
  | tps = delimited(LANGLE, separated_nonempty_list(COMMA, ID), RANGLE)
    { tps }
  |                             /* empty */
    { [] }

/* statements */
rhs:
  | e = expr(NOLEM); attrs = list(attribute)
    { (e, attrs) }

stmt:
  | s = stmt_assert { s }
  | s = stmt_assume { s }
  | s = stmt_block  { Syntax.ParserPass.Prog.SBlock s }
  | s = stmt_if     { Syntax.ParserPass.Prog.SIf s }
  /* NOTE: I don't see how we can parse a case branch without curly braces around
  the tree... */
  | MATCH; scrut = expr(yeslem); tr = delimited(LBRACE, list(stmt_case), RBRACE)
    { Syntax.ParserPass.Prog.(
        SMatch (scrut, tr))
    }
  /* NOTE: only rhs supported is expressions */
  | RETURN; rets = separated_list(COMMA, rhs)
    { Syntax.ParserPass.Prog.SReturn rets }
  | s = stmt_updandcall { s }
  | s = stmt_vardecl    { s }

stmt_assert:
  | ASSERT; attrs = list(attribute); /* option label */
    e = expr(NOLEM);
    by = endrule(SEMI { [] } | xs = stmt_block {xs});
    { Syntax.ParserPass.Prog.(
        SAssert (attrs, e, by)
    )}

stmt_assume:
  | ASSUME; attrs = list(attribute); e = expr(NOLEM); SEMI
    { Syntax.ParserPass.Prog.(
        SAssume (attrs, e))}

stmt_block:
  | xs = delimited(LBRACE, list(stmt), RBRACE) { xs }

stmt_if:
  | IF; g = expr(yeslem); t = stmt_block; e = option(stmt_if_footer)
    { { guard = g; then_br = t; footer = e } }

stmt_if_footer:
  | ELSE; elif = stmt_if
    { Syntax.ParserPass.Prog.ElseIf elif }
  | ELSE; e = stmt_block
    { Syntax.ParserPass.Prog.ElseBlock e }

stmt_case:
  | CASE; p = extended_pattern; ARROW; br = list(stmt)
   { (p, br) }

lhs:
  | x = name_seg; suffs = list(suffix);
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          x suffs)
    }
  | e = constatom_expr; suffs = nonempty_list(suffix);
    { Syntax.ParserPass.Prog.(
        List.fold_left
          (fun x y -> Suffixed (x, y))
          e suffs)
    }

stmt_updandcall:
  | lhs = lhs; list(attribute); SEMI;
    { Syntax.ParserPass.Prog.(
        SUpdAndCall (Internal.NonEmptyList.singleton lhs, []))
    }
  | lhss = midrule(lhss = separated_nonempty_list(COMMA, lhs) { Internal.NonEmptyList.coerce lhss });
    ASSIGN;
    rhss = separated_nonempty_list(COMMA, rhs)
    { Syntax.ParserPass.Prog.(
        SUpdAndCall (lhss, rhss))
    }

/* NOTE: no ghost, pattern assignemts */
stmt_vardecl_lhs:
  | attrs = list(attribute); x = ID; tp = option(tp);
    {
      { id = x; tp = tp; attrs = attrs }
    }
  /* | xs = separated_nonempty_list(COMMA, attrs = list(attribute); x = ID; tp = option(tp); { { id = x; tp = tp; attrs = attrs } }); */
  /*   { xs } */

stmt_vardecl:
  | VAR;
    xs = separated_nonempty_list(COMMA, stmt_vardecl_lhs);
    es = separated_nonempty_list(COMMA, rhs);
    { Syntax.ParserPass.Prog.(
        SVarDecl
          (DeclIds (xs, Assign es)))
    }

/* misc */
attribute:
  | LBRACECOLON; a = ID; args = separated_list(COMMA, expr(yeslem)); RBRACE
    { (a, args) }

/* module declarations */
qualified_module_name:
  | xs = separated_nonempty_list(DOT, ID)
    { Internal.NonEmptyList.coerce xs }

/* NOTE: misnomer, the `export` part refers to export sets, which we don't
         support */
qualified_module_export:
  | x = qualified_module_name { x }

import_mod_ref:
  | x = ID; DOT; xs = qualified_module_name
    { (None, Internal.NonEmptyList.cons x xs) }
  | x = ID; SGEQ; xs = qualified_module_name
    { (Some (Syntax.Common.Concrete, x), xs) }
  | x = ID; COLON; xs = qualified_module_name
    { (Some (Syntax.Common.Abstract, x), xs) }
  | x = ID
    { (None, Internal.NonEmptyList.singleton x) }

import:
  | IMPORT;
    op = boption(OPENED);
    r = import_mod_ref;
    { let (rf, tgt) = r in
      { opened = op
      ; mref = rf
      ; tgt = tgt }
    }

formal:
  | x = ID; COLON; t = tp
    { Syntax.ParserPass.TopDecl.Formal (x, t) }

formals:
  | ps = delimited(LPAREN, separated_list(COMMA, formal), RPAREN);
    { ps }

annotated_formals:
  | ps = formals { List.map (fun x -> (x, ())) ps }

/* TODO: parallel pipes for constructors? (like &&, ||)
   TODO: optional ids for datatype constructor's formal parameters
*/
datatype_ctor:
  | attrs = list(attribute); c = ID;
    ps = loption(formals)
    { Syntax.ParserPass.TopDecl.DataCtor (attrs, c, ps) }

datatype_ctors:
  | cs = separated_list(PIPE, datatype_ctor) { cs }

function_spec:
  | REQUIRES; e = expr(NOLEM)
    { Syntax.ParserPass.TopDecl.Requires e }
  /* | READS; e = expr */
  /*   { Syntax.ParserPass.ModuleItem.Reads e } */
  | ENSURES; e = expr(NOLEM)
    { Syntax.ParserPass.TopDecl.Ensures e }
  | DECREASES; e = expr(NOLEM)
    { Syntax.ParserPass.TopDecl.Decreases e }


/* Dafny file */
/* NOTE: `include` is an OCaml keyword */
includ:
  | INCLUDE; fp = STRING { fp }

/* TODO: Just aliases for now */
synonym_type_decl:
  | TYPE; attrs = list(attribute); n = ID;
    params = gen_params; SGEQ;
    tp = tp
    { Syntax.ParserPass.TopDecl.(
        { attrs = attrs
        ; id = n
        ; params = params
        ; rhs = Synonym tp
        })
    }

/* NOTE: no "predicate method", "function method", or named returns
   NOTE: bodies are optional (abstract modules/classes?) */
predfun_decl:
  | PREDICATE; attrs = list(attribute); p = ID;
    gen_ps = gen_params; ps = annotated_formals;
    specs = list(function_spec);
    e = delimited(LBRACE, expr(yeslem), RBRACE);
    { Syntax.ParserPass.TopDecl.(
        Predicate (false, attrs, p, gen_ps, ps, specs, e)
      )
    }
  | FUNCTION; attrs = list(attribute); p = ID;
    tp_params = gen_params; params = formals; COLON;
    tp = tp; specs = list(function_spec)
    bod = delimited(LBRACE, expr(yeslem), RBRACE);
    { Syntax.ParserPass.TopDecl.(
        Function (false, attrs, p, tp_params, params, tp, specs, bod)
      )
    }

datatype_decl:
  | DATATYPE; attrs = list(attribute);
    d = ID; tp_ps = gen_params;
    SGEQ;
    ctors = datatype_ctors;
    { (attrs, d, tp_ps, Internal.NonEmptyList.coerce ctors) }

/* TODO: declaration modifiers (abstract, ghost, static, opaque) */
module_decl:
  | MODULE; attrs = list(attribute); m = ID;
ds = delimited(LBRACE, list(top_decl), RBRACE);
    { (attrs, m, ds) }

methlem_keyword:
  | METHOD { Syntax.ParserPass.TopDecl.Method }
  | LEMMA  { Syntax.ParserPass.TopDecl.Lemma  }

/* NOTE: modifies clause not supported
*/
methlem_spec:
  | REQUIRES; e = expr(NOLEM)
    { Syntax.ParserPass.TopDecl.MRequires e }
  | ENSURES; e = expr(NOLEM)
    { Syntax.ParserPass.TopDecl.MEnsures e }
  | DECREASES; e = expr(NOLEM)
    { Syntax.ParserPass.TopDecl.MDecreases e }
/* | MODIFIES */

/* NOTE: for constructors, identifier is not present
** NOTE: no cardinality type (b/c no least, greatest lemmas)
** NOTE: in general the body is optional (for abstract classes/modules?)
*/
methlem_decl:
  | ml_key = methlem_keyword;
    attrs = list(attribute); id = ID;
    tp_params = gen_params; params = formals;
    spec = list(methlem_spec);
    body = stmt_block;
    { { sort = ml_key
      ; attrs = attrs
      ; id = id
      ; signature =
          { generic_params = tp_params
          ; params = params }
      ; spec = spec
      ; body = body }
    }

top_decl:
  | i = import
    { Syntax.ParserPass.TopDecl.(
        ([], ModuleImport i)
      )
    }
  | data_decl = datatype_decl;
    { Syntax.ParserPass.TopDecl.(
        ([], DatatypeDecl data_decl)
      )
    }
  | pf = predfun_decl
    { Syntax.ParserPass.TopDecl.(
        ([], PredFunDecl pf)
      )
    }
  | ml = methlem_decl
    { Syntax.ParserPass.TopDecl.(
        ([], MethLemDecl ml))
    }
  | tpd = synonym_type_decl
    { Syntax.ParserPass.TopDecl.(
        ([], SynonymTypeDecl tpd)
      )
    }
  | m = module_decl
    { Syntax.ParserPass.TopDecl.(
        ([], ModuleDef m))
    }

dafny:
  | includes = list(includ); decls = list(top_decl); EOF
    { Syntax.ParserPass.(
        Dafny {includes = includes; decls = decls })
    }
