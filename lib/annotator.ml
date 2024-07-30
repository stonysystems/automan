open Syntax
open Internal

module Convert  = Syntax.Convert (TrivMetaData) (AnnotationMetaData)
module NameSpace = NameResolution.NameSpace
module Resolver  = NameResolution.Resolver

open struct
  let ( let< )  = Result.( let< )
  let ( let<* ) = StateError.bind
end


(* BEGIN expressions
   NOTE: for now, this does nothing
*)
let attribute_handler (_: ParserPass.Prog.attribute_t list)
  : AnnotationPass.Prog.attribute_t list
  = []

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
  | ArgList (args, ()) ->
    (* TODO: this needs reworking (lookup in PMD) *)
    ArgList (List.map annotate_expr args, None)

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

let rec annotate_topdecl
  (anns: Annotation.toplevel_t) (d: ParserPass.TopDecl.t')
  : AnnotationPass.TopDecl.t' Resolver.m =
  match d with
  (* Declarations that modify the namespace *)
  | ParserPass.TopDecl.ModuleImport imp ->
    let<* () = Resolver.push_import imp anns in
    StateError.return (AnnotationPass.TopDecl.ModuleImport imp)
  | ParserPass.TopDecl.ModuleDef (m_attrs, m_id, m_decls) ->
    let<* () = Resolver.enter_module m_id anns in
    let<* m_decls' = annotate_topdecls anns m_decls in
    StateError.return begin
      AnnotationPass.TopDecl.ModuleDef
        (attribute_handler m_attrs, m_id, m_decls')
    end

  (* Declarations that don't modify the namespace
     NOTE: assume an unknown function call is all input mode *)
  | ParserPass.TopDecl.DatatypeDecl dat ->
    StateError.return
      (AnnotationPass.TopDecl.DatatypeDecl
         (Convert.datatype attribute_handler dat))
  | ParserPass.TopDecl.SynonymTypeDecl syn ->
    StateError.return
      (AnnotationPass.TopDecl.SynonymTypeDecl
         (Convert.synonym_type attribute_handler syn))
  | ParserPass.TopDecl.MethLemDecl _ ->
    failwith ("annotator: annotate_toplevel: TODO: methods/lemmas: " ^ ParserPass.TopDecl.(show_t' d))
  | ParserPass.TopDecl.PredFunDecl (Function (_, _, id, _, _, _, _, _)) ->
    failwith ("annotator: annotate_toplevel: TODO functions (" ^ id ^ ")")
  | ParserPass.TopDecl.PredFunDecl
      (Predicate (method_present, p_attrs, p_id, p_tp_params, p_params, p_specs, p_body)) ->
    let<* (_, p_ann_modes) = Resolver.find_predicate_local_decl p_id in
    if List.(length p_params <> length p_ann_modes) then
      StateError.error
        ("annotator: annotate_toplevel: mismatched arity for predicate: "
         ^ p_id)
    else begin
      let p_attrs' = attribute_handler p_attrs in
      let p_params' = List.map2 annotate_formal p_params p_ann_modes in
      let p_specs' = List.map annotate_function_spec p_specs in
      (* TODO: annotate predicate calls in expressions, too *)
      let p_body' = annotate_expr p_body in
      StateError.return begin
        AnnotationPass.TopDecl.PredFunDecl
          (Predicate
             ( method_present, p_attrs', p_id, p_tp_params
             , p_params', p_specs', p_body'))
      end
    end

and annotate_topdecls
  (anns: Annotation.toplevel_t) (ds: ParserPass.TopDecl.t list)
  : AnnotationPass.TopDecl.t list Resolver.m =
  (* : (AnnotationPass.TopDecl.t list, string) Result.t = *)
  let rec aux decls accum =
    match decls with
    | [] -> StateError.return accum
    | ((d_mods, d) :: decls) ->
      let<* d' = annotate_topdecl anns d in
      aux decls ((d_mods, d') :: accum)
  in
  StateError.map List.rev (aux ds [])

let annotate
    (a: Annotation.toplevel_t) (d: ParserPass.t)
  : (AnnotationPass.t, string) Result.t =
  let Dafny { includes = includes; decls = decls } = d in
  let< ds = State.run (annotate_topdecls a decls) NameSpace.TopLevel in
  Result.Ok AnnotationPass.(Dafny { includes = includes; decls = ds })

(* END TopDecls *)
