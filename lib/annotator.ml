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

let rec annotate_expr
    (e: ParserPass.Prog.expr_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.Prog.expr_t Resolver.m =
  match e with
  (* Suffixes *)
  | Suffixed (e, suff) -> begin
      match suff with
      | ArgList (args, ()) ->
        annotate_expr_arglist e args anns
      | AugDot (dotsuf, tp_inst) ->
        let<* e' = annotate_expr e anns in
        StateError.return AnnotationPass.Prog.(
          Suffixed (e', AugDot (dotsuf, List.map Convert.typ tp_inst)))
      | DataUpd upds ->
        let<* e' = annotate_expr e anns in
        let<* upds' =
          StateError.mapM (function | (mem_id, e_new) ->
              let<* e_new' = annotate_expr e_new anns in
              StateError.return (mem_id, e_new'))
            (NonEmptyList.as_list upds) in
        StateError.return AnnotationPass.Prog.(
          Suffixed (e', DataUpd (NonEmptyList.coerce upds')))
      | Subseq {lb = lb; ub = ub} ->
        let<* e' = annotate_expr e anns in
        (* TODO: another missing monadic combinator... *)
        let<* lb' = StateError.mapM_option (fun e -> annotate_expr e anns) lb in
        let<* ub' = StateError.mapM_option (fun e -> annotate_expr e anns) ub in
        StateError.return AnnotationPass.Prog.(
            Suffixed (e', Subseq {lb = lb'; ub = ub'}))
      | SliceLen {sublens = lens; to_end = to_end} ->
        let<* e' = annotate_expr e anns in
        let<* lens' =
          StateError.mapM (fun l -> annotate_expr l anns) (NonEmptyList.as_list lens) in
        StateError.return AnnotationPass.Prog.(
          Suffixed (e', SliceLen {sublens = NonEmptyList.coerce lens'; to_end = to_end}))
      | SeqUpd {idx = idx; v = valu} ->
        let<* e' = annotate_expr e anns in
        let<* idx' = annotate_expr idx anns in
        let<* valu' = annotate_expr valu anns in
        StateError.return AnnotationPass.Prog.(
          Suffixed (e', SeqUpd {idx = idx'; v = valu'}))
      | Sel idx ->
        let<* e' = annotate_expr e anns in
        let<* idx' = annotate_expr idx anns in
        StateError.return AnnotationPass.Prog.(
          Suffixed (e', Sel idx'))
    end
  | NameSeg (id, tp_inst) ->
    StateError.return
      (AnnotationPass.Prog.NameSeg (id, List.map Convert.typ tp_inst))
  | Lambda (params, body) ->
    let<* body' = annotate_expr body anns in
    let params' =
      List.map (function (id, tp) -> (id, Option.map Convert.typ tp)) params in
    StateError.return
      AnnotationPass.Prog.(Lambda (params', body'))
  | MapDisplay es ->
    let<* es' =
      StateError.mapM begin function (k, v) ->
        let<* k' = annotate_expr k anns in
        let<* v' = annotate_expr v anns in
        StateError.return (k', v')
      end es in
    StateError.return (AnnotationPass.Prog.MapDisplay es')
  | SeqDisplay sd -> begin
      let<* sd' = match sd with
      | SeqEnumerate es ->
        let<* es' = StateError.mapM (fun e -> annotate_expr e anns) es in
        StateError.return AnnotationPass.Prog.(SeqEnumerate es')
      | SeqTabulate {gen_inst = tps; len = l; func = f} ->
        let tps' = List.map Convert.typ tps in
        let<* l' = annotate_expr l anns in
        let<* f' = annotate_expr f anns in
        StateError.return AnnotationPass.Prog.(
            SeqTabulate { gen_inst = tps'; len = l'; func = f'})
      in
      StateError.return AnnotationPass.Prog.(SeqDisplay sd')
    end
  | SetDisplay es ->
    let<* es' = StateError.mapM (fun e -> annotate_expr e anns) es in
    StateError.return AnnotationPass.Prog.(SetDisplay es')
  | If (guard, then_, else_) ->
    let<* guard' = annotate_expr guard anns in
    let<* then_' = annotate_expr then_ anns in
    let<* else_' = annotate_expr else_ anns in
    StateError.return AnnotationPass.Prog.(
        If (guard', then_', else_'))
  | Match (scrut, tree) ->
    let<* scrut' = annotate_expr scrut anns in
    let<* tree' = StateError.mapM (fun b -> annotate_case_branch b anns) tree in
    StateError.return AnnotationPass.Prog.(
      Match (scrut', tree'))
  | Quantifier {qt = qt; qdom = qdom; qbody = qbody} ->
    let<* qdom' = annotate_quantifier_domain qdom anns in
    let<* qbody' = annotate_expr qbody anns in
    StateError.return AnnotationPass.Prog.(
        Quantifier {qt = qt; qdom = qdom'; qbody = qbody'})
  | SetComp (qdom, e) ->
    let<* qdom' = annotate_quantifier_domain qdom anns in
    let<* e' = StateError.mapM_option (fun e -> annotate_expr e anns) e in
    StateError.return AnnotationPass.Prog.(
        SetComp (qdom', e'))
  | StmtInExpr (_, _) ->
    failwith "TODO: StmtInExpr unsupported"
  | Let {ghost = ghost; pats = pats; defs = defs; body = body} ->
    let pats' = NonEmptyList.map Convert.pattern pats in
    let<* defs' = StateError.mapM (fun e -> annotate_expr e anns) (NonEmptyList.as_list defs) in
    let<* body' = annotate_expr body anns in
    StateError.return AnnotationPass.Prog.(
        Let { ghost = ghost
            ; pats = pats'
            ; defs = NonEmptyList.coerce defs'
            ; body = body'})
  | MapComp {qdom = qdom; key = k; valu = v} ->
    let<* qdom' = annotate_quantifier_domain qdom anns in
    let<* k' = StateError.mapM_option (fun e -> annotate_expr e anns) k in
    let<* v' = annotate_expr v anns in
    StateError.return AnnotationPass.Prog.(
        MapComp {qdom = qdom'; key = k'; valu = v'})
  | Lit l ->
    StateError.return AnnotationPass.Prog.(Lit l)
  | This ->
    StateError.error "annotate_expr: `this` not supported"
  | Cardinality e ->
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.Prog.(Cardinality e')
  | Tuple es ->
    let<* es' = StateError.mapM (fun e -> annotate_expr e anns) es in
    StateError.return AnnotationPass.Prog.(Tuple es')
  | Unary (uop, e) ->
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.Prog.(Unary (uop, e'))
  | Binary (bop, e1, e2) ->
    let<* e1' = annotate_expr e1 anns in
    let<* e2' = annotate_expr e2 anns in
    StateError.return AnnotationPass.Prog.(
        Binary (bop, e1', e2'))
  | Lemma {lem = lem; e = body} ->
    let<* lem' = annotate_expr lem anns in
    let<* body' = annotate_expr body anns in
    StateError.return AnnotationPass.Prog.(
        Lemma {lem = lem'; e = body'})

(* match e with *)
(* | Suffixed (e, suf) -> *)
(*   Suffixed (annotate_expr e, annotate_suffix suf) *)
(* | NameSeg (id, gen_inst) -> *)
(*   NameSeg (id, List.map Convert.typ gen_inst) *)
(* | Lambda (params, e) -> *)
(*   let params' = *)
(*     List.map *)
(*       (function (id, tp) -> *)
(*           (id, Option.map Convert.typ tp)) *)
(*       params in *)
(*   let e' = annotate_expr e in *)
(*   Lambda (params', e') *)
(* | MapDisplay es -> *)
(*   let es' = *)
(*     List.map *)
(*       (function (k, v) -> (annotate_expr k, annotate_expr v)) *)
(*       es in *)
(*   MapDisplay es' *)
  (* | SeqDisplay ed -> *)
  (*   SeqDisplay begin match ed with *)
  (*     | SeqEnumerate es -> *)
  (*       SeqEnumerate (List.map annotate_expr es) *)
  (*     | SeqTabulate *)
  (*         { gen_inst = gen_inst; len = len; func = func} -> *)
  (*       SeqTabulate *)
  (*         { gen_inst = List.map Convert.typ gen_inst *)
  (*         ; len = annotate_expr len *)
  (*         ; func = annotate_expr func } *)
  (*   end *)
  (* | SetDisplay elems -> *)
  (*   SetDisplay (List.map annotate_expr elems) *)
  (* | If (g, t, e) -> *)
  (*   If (annotate_expr g *)
  (*      , annotate_expr t *)
  (*      , annotate_expr e) *)
  (* | Match (scrut, tree) -> *)
  (*   let annotate_branch = function *)
  (*     | ParserPass.Prog.Case (attrs, pat, body) -> *)
  (*       AnnotationPass.Prog.Case *)
  (*         ( attribute_handler attrs *)
  (*         , Convert.extended_pattern pat *)
  (*         , annotate_expr body) *)
  (*   in *)
  (*   Match (annotate_expr scrut, List.map annotate_branch tree) *)
  (* | Quantifier { qt = qt; qdom = qdom; qbody = body } -> *)
  (*   Quantifier *)
  (*     { qt = qt *)
  (*     ; qdom = annotate_quantifier_domain qdom *)
  (*     ; qbody = annotate_expr body } *)
  (* | SetComp (qdom, e) -> *)
  (*   SetComp *)
  (*     ( annotate_quantifier_domain qdom *)
  (*     , Option.map annotate_expr e) *)
  (* | StmtInExpr (_, _) -> *)
  (*   failwith "TODO: annotate StmtInExpr" *)
  (* | Let { ghost = ghost; pats = pats; defs = defs; body = body } -> *)
  (*   Let *)
  (*     { ghost = ghost *)
  (*     ; pats = NonEmptyList.map Convert.pattern pats *)
  (*     ; defs = NonEmptyList.map annotate_expr defs *)
  (*     ; body = annotate_expr body } *)
  (* | MapComp { qdom = qdom; key = key; valu = valu } -> *)
  (*   MapComp *)
  (*     { qdom = annotate_quantifier_domain qdom *)
  (*     ; key = Option.map annotate_expr key *)
  (*     ; valu = annotate_expr valu } *)
  (* | Lit lit -> Lit lit *)
  (* | This -> This *)
  (* | Cardinality e -> Cardinality (annotate_expr e) *)
  (* | Tuple es -> Tuple (List.map annotate_expr es) *)
  (* | Unary (op, e) -> Unary (op, annotate_expr e) *)
  (* | Binary (op, e1, e2) -> *)
  (*   Binary( op, annotate_expr e1, annotate_expr e2) *)
  (* | Lemma { lem = lem; e = e } -> *)
  (*   Lemma {lem = annotate_expr lem; e = annotate_expr e } *)

and annotate_expr_arglist
    (f: ParserPass.Prog.expr_t) (args: ParserPass.Prog.expr_t list) (anns: Annotation.toplevel_t)
  : AnnotationPass.Prog.expr_t Resolver.m =
  (* NOTE: This pass does not try to determine if the usages of predicates
     are sensible; it only tries to make sure that every invocation in the
     AST of a predicate the user has annotated is decorated with that annotation *)
    let<* args' =
      StateError.mapM (fun a -> annotate_expr a anns) args in
    match ParserPass.Prog.maybe_to_qualified_id f with
    | None ->
      (* `f` is not a qualified identifier, so we couldn't hope to know what the
         intended annotations are without type analysis *)
      let<* f' = annotate_expr f anns in
      StateError.return AnnotationPass.Prog.(
          Suffixed (f', ArgList (args', None)))
    | Some qf_id ->
      (* `f` is a qualified identifier, so did the user provide an annotation
         for it? *)
      let f' = AnnotationPass.Prog.from_qualified_id qf_id in
      let<* maybe_p_ann = Resolver.maybe_find_predicate qf_id anns in
      match maybe_p_ann with
      | None ->
        (* No annotation found for `f`, so treat it as before *)
        StateError.return AnnotationPass.Prog.(
          Suffixed (f', (ArgList (args', None))))
      | Some (_, p_modes) ->
        StateError.return AnnotationPass.Prog.(
          Suffixed (f', ArgList (args', Some (qf_id, p_modes))))

(* and annotate_suffix = function *)
(*   | AugDot (dotsuff, gen_inst) -> *)
(*     AugDot (dotsuff, List.map Convert.typ gen_inst) *)
(*   | DataUpd upds -> *)
(*     let annotate_upd = function *)
(*       | (mem, e) -> (mem, annotate_expr e) in *)
(*     DataUpd (NonEmptyList.map annotate_upd upds) *)
(*   | Subseq { lb = lb; ub = ub } -> *)
(*     Subseq *)
(*       { lb = Option.map annotate_expr lb *)
(*       ; ub = Option.map annotate_expr ub } *)
(*   | SliceLen { sublens = sublens; to_end = to_end } -> *)
(*     SliceLen *)
(*       { sublens = NonEmptyList.map annotate_expr sublens *)
(*       ; to_end = to_end } *)
(*   | SeqUpd {idx = idx; v = v } -> *)
(*     SeqUpd *)
(*       { idx = annotate_expr idx *)
(*       ; v   = annotate_expr v } *)
(*   | Sel idx -> *)
(*     Sel (annotate_expr idx) *)
(*   | ArgList (args, ()) -> *)
(*     (\* TODO: this needs reworking (lookup in PMD) *\) *)
(*     ArgList (List.map annotate_expr args, None) *)

and annotate_case_branch
    (branch: ParserPass.Prog.case_expr_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.Prog.case_expr_t Resolver.m =
  let Case (attrs, epat, body) = branch in
  let attrs' = attribute_handler attrs in
  let epat' = Convert.extended_pattern epat in
  let<* body' = annotate_expr body anns in
  StateError.return AnnotationPass.Prog.(
    Case (attrs', epat', body'))

and annotate_quantifier_domain
    (qdom: ParserPass.Prog.qdom_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.Prog.qdom_t Resolver.m =
  let ParserPass.Prog.QDom {qvars = qvars; qrange = qrange} = qdom in
  let<* qvars' =
    StateError.mapM
      (function ParserPass.Prog.QVar (id, tp, col_dom, attrs) ->
         let tp' = Option.map Convert.typ tp in
         let<* col_dom' =
           StateError.mapM_option (fun e -> annotate_expr e anns) col_dom in
         let attrs' = attribute_handler attrs in
         StateError.return AnnotationPass.Prog.(
             QVar (id, tp', col_dom', attrs')))
      qvars
  in
  let<* qrange' = StateError.mapM_option (fun e -> annotate_expr e anns) qrange in
  StateError.return AnnotationPass.Prog.(
    QDom { qvars = qvars'; qrange = qrange'})
(* END expressions *)

(* BEGIN TopDecls (utilities) *)
let annotate_formal
    (p: ParserPass.TopDecl.formal_annotated_t) (m: Annotation.mode_t)
    : AnnotationPass.TopDecl.formal_annotated_t =
  let (Formal (id, tp), ()) = p in
  (Formal (id, Convert.typ tp), m)
(* END TopDecls (utilities) *)

let annotate_function_spec
    (spec: ParserPass.TopDecl.function_spec_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.TopDecl.function_spec_t Resolver.m =
  match spec with
  | Requires e ->
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.TopDecl.(
        Requires e')
  | Reads e ->
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.TopDecl.(
        Reads e')
  | Ensures e ->
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.TopDecl.(
        Ensures e')
  | Decreases e ->
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.TopDecl.(
        Decreases e')

let rec annotate_topdecl
  (anns: Annotation.toplevel_t) (d: ParserPass.TopDecl.t')
  : AnnotationPass.TopDecl.t' Resolver.m =
  match d with
  (* Declarations that modify the namespace *)
  | ParserPass.TopDecl.ModuleImport imp ->
    (* NOTE: if we fail to find the imported module, assume the user did not
       have anything they wished to annotate there *)
    let<* _ = Resolver.push_import imp anns in
    StateError.return (AnnotationPass.TopDecl.ModuleImport imp)
  | ParserPass.TopDecl.ModuleDef (m_attrs, m_id, m_decls) ->
    Resolver.within_module m_id anns begin
      let<* m_decls' = annotate_topdecls anns m_decls in
      StateError.return
        AnnotationPass.TopDecl.(
          ModuleDef (attribute_handler m_attrs, m_id, m_decls'))
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
    failwith
      ("annotator: annotate_toplevel: TODO: methods/lemmas: "
       ^ ParserPass.TopDecl.(show_t' d))
  | ParserPass.TopDecl.PredFunDecl (Function (_, _, id, _, _, _, _, _)) ->
    failwith
      ("annotator: annotate_toplevel: TODO functions:"
       ^ id)
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
      let<* p_specs' =
        StateError.mapM (fun spec -> annotate_function_spec spec anns) p_specs in
      (* TODO: annotate predicate calls in expressions, too *)
      let<* p_body' = annotate_expr p_body anns in
      StateError.return AnnotationPass.TopDecl.(
          PredFunDecl
            (Predicate
               ( method_present, p_attrs', p_id, p_tp_params
               , p_params', p_specs', p_body')))
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
