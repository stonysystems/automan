open Syntax
open Internal

open struct
  let ( let< ) = Result.( let< )
end

module Convert = Syntax.Convert (TrivMetaData) (AnnotationMetaData)

(* BEGIN expressions
   NOTE: for now, this does nothing
*)
let rec annotate_expr (e: ParserPass.Prog.expr_t)
  : AnnotationPass.Prog.expr_t =
  match e with
  | Suffixed (e, suf) ->
    Suffixed (annotate_expr e, annotate_suffix suf)
  | NameSeg (id, gen_inst) ->
    NameSeg (id, List.map Convert.typ gen_inst)
  | Lambda (params, e) ->
    let params' =
      List.map
        (function (id, tp) ->
            (id, Option.map Convert.typ tp))
        params in
    let e' = annotate_expr e in
    Lambda (params', e')
  | MapDisplay es ->
    let es' =
      List.map
        (function (k, v) -> (annotate_expr k, annotate_expr v))
        es in
    MapDisplay es'
  | SeqDisplay ed ->
    SeqDisplay begin match ed with
      | SeqEnumerate es ->
        SeqEnumerate (List.map annotate_expr es)
      | SeqTabulate
          { gen_inst = gen_inst; len = len; func = func} ->
        SeqTabulate
          { gen_inst = List.map Convert.typ gen_inst
          ; len = annotate_expr len
          ; func = annotate_expr func }
    end
  | SetDisplay elems ->
    SetDisplay (List.map annotate_expr elems)
  | If (g, t, e) ->
    If (annotate_expr g
       , annotate_expr t
       , annotate_expr e)
  | Match (scrut, tree) ->
    let annotate_branch = function
      | ParserPass.Prog.Case (attrs, pat, body) ->
        AnnotationPass.Prog.Case
          ( attribute_handler attrs
          , Convert.extended_pattern pat
          , annotate_expr body)
    in
    Match (annotate_expr scrut, List.map annotate_branch tree)
  | Quantifier { qt = qt; qdom = qdom; qbody = body } ->
    Quantifier
      { qt = qt
      ; qdom = annotate_quantifier_domain qdom
      ; qbody = annotate_expr body }
  | SetComp (qdom, e) ->
    SetComp
      ( annotate_quantifier_domain qdom
      , Option.map annotate_expr e)
  | StmtInExpr (_, _) ->
    failwith "TODO: annotate StmtInExpr"
  | Let { ghost = ghost; pats = pats; defs = defs; body = body } ->
    Let
      { ghost = ghost
      ; pats = NonEmptyList.map Convert.pattern pats
      ; defs = NonEmptyList.map annotate_expr defs
      ; body = annotate_expr body }
  | MapComp { qdom = qdom; key = key; valu = valu } ->
    MapComp
      { qdom = annotate_quantifier_domain qdom
      ; key = Option.map annotate_expr key
      ; valu = annotate_expr valu }
  | Lit lit -> Lit lit
  | This -> This
  | Cardinality e -> Cardinality (annotate_expr e)
  | Tuple es -> Tuple (List.map annotate_expr es)
  | Unary (op, e) -> Unary (op, annotate_expr e)
  | Binary (op, e1, e2) ->
    Binary( op, annotate_expr e1, annotate_expr e2)
  | Lemma { lem = lem; e = e } ->
    Lemma {lem = annotate_expr lem; e = annotate_expr e }

and annotate_suffix = function
  | AugDot (dotsuff, gen_inst) ->
    AugDot (dotsuff, List.map Convert.typ gen_inst)
  | DataUpd upds ->
    let annotate_upd = function
      | (mem, e) -> (mem, annotate_expr e) in
    DataUpd (NonEmptyList.map annotate_upd upds)
  | Subseq { lb = lb; ub = ub } ->
    Subseq
      { lb = Option.map annotate_expr lb
      ; ub = Option.map annotate_expr ub }
  | SliceLen { sublens = sublens; to_end = to_end } ->
    SliceLen
      { sublens = NonEmptyList.map annotate_expr sublens
      ; to_end = to_end }
  | SeqUpd {idx = idx; v = v } ->
    SeqUpd
      { idx = annotate_expr idx
      ; v   = annotate_expr v }
  | Sel idx ->
    Sel (annotate_expr idx)
  | ArgList args ->
    ArgList (List.map annotate_expr args)

and annotate_quantifier_domain (qdom: ParserPass.Prog.qdom_t)
  : AnnotationPass.Prog.qdom_t =
  let QDom { qvars = qvars; qrange = qrange } = qdom in
  let annotate_qvar = function
    | ParserPass.Prog.QVar (id, tp, col, attrs) ->
      AnnotationPass.Prog.QVar
        ( id, Option.map Convert.typ tp
        , Option.map annotate_expr col, attribute_handler attrs) in
  let qvars' = List.map annotate_qvar qvars in
  let qrange' = Option.map annotate_expr qrange in
  QDom { qvars = qvars'; qrange = qrange' }

and attribute_handler (_: ParserPass.Prog.attribute_t list): AnnotationPass.Prog.attribute_t list
  = []
(* END expressions *)

(* BEGIN TopDecls (utilities) *)
let annotate_formal
    (p: ParserPass.TopDecl.formal_annotated_t) (m: Annotation.mode_t)
    : AnnotationPass.TopDecl.formal_annotated_t =
  let (Formal (id, tp), ()) = p in
  (Formal (id, Convert.typ tp), m)
(* END TopDecls (utilities) *)

let annotate_function_spec (spec: ParserPass.TopDecl.function_spec_t)
  : AnnotationPass.TopDecl.function_spec_t =
  match spec with
  | Requires e -> Requires (annotate_expr e)
  | Reads e -> Reads (annotate_expr e)
  | Ensures e -> Ensures (annotate_expr e)
  | Decreases e -> Decreases (annotate_expr e)

(* BEGIN TopDecls *)
let rec annotate_toplevel
    (a: Annotation.toplevel_t) (d: ParserPass.TopDecl.t)
  : ((Annotation.toplevel_t * AnnotationPass.TopDecl.t), string) Result.t =
  let (mods, d') = d in
  match (a, d') with
  (* skip *)
  | (_, ParserPass.TopDecl.ModuleImport imp) ->
    Result.Ok (a, (mods, AnnotationPass.TopDecl.ModuleImport imp))
  | (_, ParserPass.TopDecl.DatatypeDecl dat) ->
    Result.Ok
      (a, (mods
          , AnnotationPass.TopDecl.DatatypeDecl
              (Convert.datatype attribute_handler dat)))
  | (_, ParserPass.TopDecl.SynonymTypeDecl syn) ->
    Result.Ok
      (a, (mods
          , AnnotationPass.TopDecl.SynonymTypeDecl
              (Convert.synonym_type attribute_handler syn)))
  | (_, ParserPass.TopDecl.MethLemDecl _) ->
    failwith ("TODO: methods/lemmas: " ^ ParserPass.TopDecl.(show d))
  | (_, ParserPass.TopDecl.PredFunDecl (Function (_, _, id, _, _, _, _, _))) ->
    failwith ("annotator: annotate_toplevel: TODO functions (" ^ id ^ ")")
  (* process *)
  | ([], _) ->
    Result.Error
      ("annotator: annotate_toplevel: reached end of annotations, but more remain\n"
       ^ ParserPass.TopDecl.(show d))
  | (Annotation.Module (id, anns') :: anns
    , ParserPass.TopDecl.ModuleDef (attrs, m_id, m_ds)) ->
    if id <> m_id then
      Result.Error
        ("annotator: annotate_toplevel: mismatched module names\n"
         ^ "- annotation:  " ^ id ^ "\n"
         ^ "- declaration: " ^ m_id)
    else begin
      let< m_ds' = annotate_toplevels anns' m_ds in
      Result.Ok
        (anns, (mods
               , AnnotationPass.TopDecl.ModuleDef
                   (attribute_handler attrs, m_id, m_ds')))
    end
  | (Annotation.Predicate (id, modes) :: anns
    , ParserPass.TopDecl.PredFunDecl
       (Predicate (method_present, attrs, p_id, tp_params, params, specs, body))) ->
    if id <> p_id then
      Result.Error
        ("annotator: annotate_toplevel: mismatched predicate names\n"
         ^ "- annotation: " ^ id ^ "\n"
         ^ "- predicate:  " ^ p_id)
    else if List.(length params <> length modes) then
      Result.Error
        ("annotator: annotate_toplevel: mismatched arity for predicate: " ^ p_id)
    else begin
      let attrs'  = attribute_handler attrs in
      let params' = List.map2 annotate_formal params modes in
      Result.Ok
        ( anns
        , ( mods
          , AnnotationPass.TopDecl.PredFunDecl
              (Predicate
                 (method_present, attrs', p_id, tp_params
                 , params', List.map annotate_function_spec specs
                 , annotate_expr body))))
    end
  | (ann :: _, _) ->
    Result.Error
      ("annotator: annotate_toplevel: mismatched annotation and toplevel declaration (did you forget an annotation?)\n"
       ^ "- annotation:  " ^ Annotation.show ann ^ "\n"
       ^ "- declaration: " ^ ParserPass.TopDecl.show d)

(* TODO: This expects the annotations are in the same order that they appear in
   the Dafny file *)
and annotate_toplevels
    (a: Annotation.toplevel_t) (ds: ParserPass.TopDecl.t list) =
  let rec aux a ds accum =
    match (a , ds) with
    | ([], []) -> Result.Ok accum
    | (ann :: _, []) ->
      Result.Error
        ("annotator: annotate_toplevels: missing toplevel declaration for annotation\n"
         ^ "- annotation: " ^ Annotation.show ann)
    | (_, d :: ds) ->
      let< (anns', d') = annotate_toplevel a d in
      aux anns' ds (d' :: accum)
  in
  Result.map List.rev (aux a ds [])

let annotate
    (a: Annotation.toplevel_t) (d: ParserPass.t): (AnnotationPass.t, string) Result.t =
  let Dafny { includes = includes; decls = decls } = d in
  let< ds = annotate_toplevels a decls in
  Result.Ok AnnotationPass.(Dafny { includes = includes; decls = ds })

(* END TopDecls *)
