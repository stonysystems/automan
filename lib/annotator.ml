open Syntax
open Internal

module AnnotationMetaData : MetaData
  with type predicate_decl_t  = Annotation.mode_t list option

  with type ite_t            = unit
  with type match_t          = unit
  with type quantification_t = unit
  with type binary_op_t      = unit

  with type arglist_t = (id_t NonEmptyList.t * Annotation.mode_t list) option
= struct
  (** - When this is Option.None, the user did not provide an annotation for
        this predicate. For now, a sensible default is to assume all arguments are
        input moded; however, since this might change it is desirable to
        distinguish this case from the case where the user provides an explicit
        annotation indicating all arguments should be input moded

      - When this is Option.Some modes, `List.length modes` is exactly the arity
        of the predicate *)
  type predicate_decl_t  = Annotation.mode_t list option
  [@@deriving show, eq]

  type ite_t = unit
  [@@deriving show, eq]

  type match_t = unit
  [@@deriving show, eq]

  type quantification_t = unit
  [@@deriving show, eq]

  type binary_op_t = unit
  [@@deriving show, eq]

  (** - When this is Option.None, the call is not associated with a known
        predicate. For now, assume this means all arguments are input moded

      - When this is Option.Some, the mode list this contains has the same
        length as the argument list suffix, and the expression to which the
        call is attached is given the qualified identifier
  *)
  type arglist_t = (id_t NonEmptyList.t * Annotation.mode_t list) option
  [@@deriving show, eq]
end

module AnnotationPass = AST (AnnotationMetaData)

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
  | If ((), guard, then_, else_) ->
    let<* guard' = annotate_expr guard anns in
    let<* then_' = annotate_expr then_ anns in
    let<* else_' = annotate_expr else_ anns in
    StateError.return AnnotationPass.Prog.(
        If ((), guard', then_', else_'))
  | Match ((), scrut, tree) ->
    let<* scrut' = annotate_expr scrut anns in
    let<* tree' = StateError.mapM (fun b -> annotate_case_branch b anns) tree in
    StateError.return AnnotationPass.Prog.(
      Match ((), scrut', tree'))
  | Quantifier ((), {qt = qt; qdom = qdom; qbody = qbody}) ->
    let<* qdom' = annotate_quantifier_domain qdom anns in
    let<* qbody' = annotate_expr qbody anns in
    StateError.return AnnotationPass.Prog.(
        Quantifier ((), {qt = qt; qdom = qdom'; qbody = qbody'}))
  | SetComp {qdom = qdom; body = body} ->
    let<* qdom' = annotate_quantifier_domain qdom anns in
    let<* body' = StateError.mapM_option (fun e -> annotate_expr e anns) body in
    StateError.return AnnotationPass.Prog.(
        SetComp {qdom = qdom'; body = body'})
  | StmtInExpr (stmt, e) ->
    let<* stmt' = annotate_stmt_in_expr stmt anns in
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.Prog.(StmtInExpr (stmt', e'))
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
  | Binary ((), bop, e1, e2) ->
    let<* e1' = annotate_expr e1 anns in
    let<* e2' = annotate_expr e2 anns in
    StateError.return AnnotationPass.Prog.(
        Binary ((), bop, e1', e2'))
  | Lemma {lem = lem; e = body} ->
    let<* lem' = annotate_expr lem anns in
    let<* body' = annotate_expr body anns in
    StateError.return AnnotationPass.Prog.(
        Lemma {lem = lem'; e = body'})

and annotate_expr_arglist
    (f: ParserPass.Prog.expr_t) (args: ParserPass.Prog.arglist_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.Prog.expr_t Resolver.m =
  (* NOTE: This pass does not try to determine if the usages of predicates
     are sensible; it only tries to make sure that every invocation in the
     AST of a predicate the user has annotated is decorated with that annotation *)
  let (args_pos, args_named) = (args.positional, args.named) in
  let<* args_pos' =
    StateError.mapM (fun a -> annotate_expr a anns) args_pos in
  let<* args_named' =
    StateError.mapM begin function (id, a) ->
      let<* a' = annotate_expr a anns in
      StateError.return (id, a')
    end args_named
  in
  let args': AnnotationPass.Prog.arglist_t =
    { positional = args_pos' ; named = args_named' } in
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

and annotate_stmt_in_expr
    (stmt: ParserPass.Prog.stmt_in_expr_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.Prog.stmt_in_expr_t Resolver.m =
  match stmt with
  | Assert (attrs, assertion, block) ->
    let attrs' = attribute_handler attrs in
    let<* assertion' = annotate_expr assertion anns in
    let<* block' = StateError.mapM (fun s -> annotate_stmt s anns) block in
    StateError.return AnnotationPass.Prog.(
        Assert (attrs', assertion', block'))
  | Assume (attrs, assumption) ->
    let attrs' = attribute_handler attrs in
    let<* assumption' = annotate_expr assumption anns in
    StateError.return AnnotationPass.Prog.(
        Assume (attrs', assumption'))
(* END expressions *)

(* BEGIN statements *)
and annotate_stmt
    (stmt: ParserPass.Prog.stmt_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.Prog.stmt_t Resolver.m =
  match stmt with
  | SAssert (attrs, assertion, block) ->
    let attrs' = attribute_handler attrs in
    let<* assertion' = annotate_expr assertion anns in
    let<* block' = annotate_stmt_block block anns in
    StateError.return AnnotationPass.Prog.(
        SAssert (attrs', assertion', block'))
  | SAssume (attrs, assumption) ->
    let attrs' = attribute_handler attrs in
    let<* assumption' = annotate_expr assumption anns in
    StateError.return AnnotationPass.Prog.(
        SAssume (attrs', assumption'))
  | SBlock block ->
    let<* block' = StateError.mapM (fun s -> annotate_stmt s anns) block in
    StateError.return AnnotationPass.Prog.(
        SBlock block')
  | SIf if_ ->
    let<* if_' = annotate_stmt_if if_ anns in
    StateError.return AnnotationPass.Prog.(
        SIf if_')
  | SMatch (scrut, case_tree) ->
    let<* scrut' = annotate_expr scrut anns in
    let<* case_tree' =
      StateError.mapM (fun br -> annotate_stmt_case br anns) case_tree in
    StateError.return AnnotationPass.Prog.(
        SMatch (scrut', case_tree'))
  | SReturn rets ->
    let<* rets': AnnotationPass.Prog.rhs_t list =
      StateError.mapM begin
        function (ret, attrs) ->
           let<* ret' = annotate_expr ret anns in
           let attrs' = attribute_handler attrs in
           StateError.return (ret', attrs')
      end rets in
    StateError.return AnnotationPass.Prog.(
        SReturn rets')
  | SUpdAndCall (lhss, rhss) ->
    let<* lhss' =
      StateError.mapM
        (fun e -> annotate_expr e anns)
        (NonEmptyList.as_list lhss)
    in let<* rhss' =
         StateError.mapM begin function (e, attrs) ->
           let<* e' = annotate_expr e anns in
           let attrs' = attribute_handler attrs in
           StateError.return (e', attrs')
         end rhss in
    StateError.return AnnotationPass.Prog.(
        SUpdAndCall (NonEmptyList.coerce lhss', rhss'))
  | SVarDecl (DeclIds (ids, rhs)) ->
    let annotate_stmt_var_decl_id_lhs
        (id: ParserPass.Prog.var_decl_id_lhs_t)
        : AnnotationPass.Prog.var_decl_id_lhs_t =
      let tp' = Option.map Convert.typ id.tp in
      let attrs' = attribute_handler id.attrs in
      {id = id.id; tp = tp'; attrs = attrs'}
    in
    let ids' = List.map annotate_stmt_var_decl_id_lhs ids in
    let<* rhs' = StateError.mapM_option begin fun r ->
        match r with
        | ParserPass.Prog.Assign rhss ->
          let<* rhss' =
            StateError.mapM begin function (e, attrs) ->
              let<* e' = annotate_expr e anns in
              let attrs' = attribute_handler attrs in
              StateError.return (e', attrs')
            end rhss in
          StateError.return AnnotationPass.Prog.(Assign rhss')
      end rhs
    in
    StateError.return AnnotationPass.Prog.(
        SVarDecl (DeclIds (ids', rhs')))

and annotate_stmt_block block anns =
  StateError.mapM (fun s -> annotate_stmt s anns) block

and annotate_stmt_if
    (if_: ParserPass.Prog.stmt_if_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.Prog.stmt_if_t Resolver.m =
  let<* g' = annotate_expr if_.guard anns in
  let<* t' = annotate_stmt_block if_.then_br anns in
  let<* footer' = StateError.mapM_option (fun f -> annotate_stmt_if_footer f anns) if_.footer in
  StateError.return AnnotationPass.Prog.(
      {guard = g'; then_br = t'; footer = footer'})


and annotate_stmt_if_footer
    (footer: ParserPass.Prog.stmt_if_footer_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.Prog.stmt_if_footer_t Resolver.m =
  match footer with
  | ElseIf if_ ->
    let<* if_' = annotate_stmt_if if_ anns in
    StateError.return AnnotationPass.Prog.(
        ElseIf if_')
  | ElseBlock block ->
    let<* block' = annotate_stmt_block block anns in
    StateError.return AnnotationPass.Prog.(
        ElseBlock block')

and annotate_stmt_case
    (branch: ParserPass.Prog.stmt_case_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.Prog.stmt_case_t Resolver.m =
  let (epats, body) = branch in
  let epats' = Convert.extended_pattern epats in
  let<* body' = annotate_stmt_block body anns in
  StateError.return (epats', body')
(* END statements *)

(* BEGIN TopDecls (utilities) *)
(* let annotate_formal *)
(*     (p: ParserPass.TopDecl.formal_annotated_t) (m: Annotation.mode_t) *)
(*     : AnnotationPass.TopDecl.formal_annotated_t = *)
(*   let (Formal (id, tp), ()) = p in *)
(*   (Formal (id, Convert.typ tp), m) *)
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

let annotate_method_spec
    (s: ParserPass.TopDecl.method_spec_t) (anns: Annotation.toplevel_t)
  : AnnotationPass.TopDecl.method_spec_t Resolver.m =
  match s with
  | MModifies e ->
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.TopDecl.(
        MModifies e')
  | MRequires e ->
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.TopDecl.(
        MRequires e')
  | MEnsures e ->
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.TopDecl.(
        MEnsures e')
  | MDecreases e ->
    let<* e' = annotate_expr e anns in
    StateError.return AnnotationPass.TopDecl.(
        MDecreases e')

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
  | ParserPass.TopDecl.MethLemDecl
      { sort = sort; attrs = attrs
      ; id = id; signature = sign; spec = spec
      ; body = body } ->
    let attrs' = attribute_handler attrs in
    let signature' = Convert.method_signature sign in
    let<* spec' =
      StateError.mapM
        (fun s -> annotate_method_spec s anns)
        spec in
    let<* body' = annotate_stmt_block body anns in
    StateError.return AnnotationPass.TopDecl.(
        MethLemDecl
          { sort = sort; attrs = attrs'
          ; id = id; signature = signature'; spec = spec'
          ; body = body' })
  | ParserPass.TopDecl.PredFunDecl
      (Function (m_pres, attrs, id, tp_ps, ps, tp, specs, body)) ->
    let attrs' = attribute_handler attrs in
    let ps' = List.map Convert.formal ps in
    let tp' = Convert.typ tp in
    let<* specs' =
      StateError.mapM
        (fun s -> annotate_function_spec s anns)
        specs in
    let<* body' = annotate_expr body anns in
    StateError.return AnnotationPass.TopDecl.(
        PredFunDecl
          (Function (m_pres, attrs', id, tp_ps, ps', tp', specs', body')))
  | ParserPass.TopDecl.PredFunDecl
      (Predicate ((), method_present, p_attrs, p_id, p_tp_params, p_params, p_specs, p_body)) ->
    let<* p_ann_modes = begin
      let<* p_ann =
        StateError.map_error ((^) "annotator.annotate_topdecl:\n")
          Resolver.(maybe_find_predicate_local_decl p_id) in
      StateError.mapM_option
        (function (_, p_ann_modes) ->
           if List.(length p_params <> length p_ann_modes) then
             StateError.error
               ("annotator.annotate_topdecl: mismatched arity for predicate: "
                ^ p_id)
           else StateError.return p_ann_modes
        )
        p_ann
    end in
    let p_attrs' = attribute_handler p_attrs in
    let p_params' = List.map Convert.formal p_params in
    let<* p_specs' =
      StateError.mapM (fun spec -> annotate_function_spec spec anns) p_specs in
    (* TODO: annotate predicate calls in expressions, too *)
    let<* p_body' = annotate_expr p_body anns in
    StateError.return AnnotationPass.TopDecl.(
        PredFunDecl
          (Predicate
             ( p_ann_modes, method_present, p_attrs'
             , p_id, p_tp_params, p_params', p_specs', p_body')))

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
