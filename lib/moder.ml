open Syntax
open Internal
open Annotator

(** The mode analysis pass does the following:
  * - checks for inconsistency between the user annotations on predicates and
  *   the usage of those predicates in the spec (e.g., checks whether a
  *   parameter marked as input is being used in an output position of another
  *   annotated predicate)
  *
  *   if an inconsistency is found, the enclosing declaration is marked as
  *   needing to have a stub (signature with no body) generated
  * - marks each node of the AST of an expression body with the output-moded
  *   formal parameters
*)
module Definitions = struct
  type unary_op_for_outvar_t = Cardinality
  [@@deriving show, eq]

  (** The LHS of assignments to (members of) out vars. Some operations (for
      now, only cardinality) can be treated as pseudo-members that we will try
      to support
  *)
  type outvar_lhs_t =
    { mq_outvar: Common.member_qualified_name_t
    ; uop: unary_op_for_outvar_t option }
  [@@deriving show, eq]

  (** - Predicate: this predicate will be translated as a predicate in the
   *    implementation
   * - Function: this predicate will be functionalized in the implementation
   *
   *   - make_stub: the predicate body is beyond our analysis, so generate a
   *     stub in the implementation (we can at least check it is used in
   *     accordance with the user's annotations)
   *   - vars_in: ordered subset of the predicate's formal parameters marked
   *     as input
   *   - vars_out: ordered subset of the predicate's formal parameters marked
   *     as output
  *)
  type predicate_decl_t =
    | Predicate
    | Function of
        { make_stub: bool
        ; vars_in:  AnnotationPass.TopDecl.formal_t list
        ; vars_out: AnnotationPass.TopDecl.formal_t NonEmptyList.t
        ; requires: AnnotationPass.Prog.expr_t list }
  [@@deriving show, eq]

  (** - vars_then: output variables in the `then` branch
    * - vars_else: output variables in the `else` branch
  *)
  type ite_functionalize_t =
    { vars_then: outvar_lhs_t NonEmptyList.t
    ; vars_else: outvar_lhs_t NonEmptyList.t }
  [@@deriving show, eq]

  (** The list of output variables in each branch *)
  type match_functionalize_t = (outvar_lhs_t NonEmptyList.t) NonEmptyList.t
  [@@deriving show, eq]

  (** The output variable mentioned in a quantification *)
  type quantification_functionalize_t = outvar_lhs_t
  [@@deriving show, eq]

  (** - outvar_is_left: true iff the (member-qualified) outvar is the left
        expression of the equation
      - outvar: the outvar in the equation
  *)
  type binary_op_functionalize_eq_t =
    { outvar_is_left: bool
    ; outvar: outvar_lhs_t
    }
  [@@deriving show, eq]

  (** The (member-qualified) outvars of both conjuncts *)
  type binary_op_functionalize_and_t =
    { conj_left:  outvar_lhs_t list
    ; conj_right: outvar_lhs_t list }
  [@@deriving show, eq]

  type binary_op_functionalize_t =
    | Eq  of binary_op_functionalize_eq_t
    | And of binary_op_functionalize_and_t
  [@@deriving show, eq]

  (** - callee: the predicate name being called
      - exprs_in: the expressions in the input positions of the argument list
      - out_vars: the member-qualified outvars in the output positioins of the
        argument list

      NOTE: if you encounter this annotation, exprs_in contains no outvars
  *)
  type arglist_functionalize_t =
    { callee: Common.module_qualified_name_t
    ; in_exprs:  ParserPass.Prog.expr_t list
    ; out_vars: Syntax.Common.member_qualified_name_t list }
  [@@deriving show, eq]
end

module ModingMetaData : MetaData
  with type predicate_decl_t    = Definitions.predicate_decl_t
  with type datatype_decl_t     = AnnotationMetaData.datatype_decl_t
  with type synonym_type_decl_t = AnnotationMetaData.synonym_type_decl_t

  with type type_t = AnnotationMetaData.type_t

  with type ite_t = Definitions.ite_functionalize_t option
  with type match_t = Definitions.match_functionalize_t option
  with type quantification_t = Definitions.quantification_functionalize_t option
  with type binary_op_t = Definitions.binary_op_functionalize_t option

  with type arglist_t = Definitions.arglist_functionalize_t option
= struct
  type predicate_decl_t = Definitions.predicate_decl_t
  [@@deriving show, eq]
  type datatype_decl_t  = AnnotationMetaData.datatype_decl_t
  [@@deriving show, eq]
  type synonym_type_decl_t = AnnotationMetaData.synonym_type_decl_t
  [@@deriving show, eq]

  type type_t = AnnotationMetaData.type_t
  [@@deriving show, eq]

  type ite_t = Definitions.ite_functionalize_t option
  [@@deriving show, eq]
  type match_t = Definitions.match_functionalize_t option
  [@@deriving show, eq]
  type quantification_t = Definitions.quantification_functionalize_t option
  [@@deriving show, eq]
  type binary_op_t = Definitions.binary_op_functionalize_t option
  [@@deriving show, eq]

  type arglist_t = Definitions.arglist_functionalize_t option
  [@@deriving show, eq]
end

module ModePass = AST (ModingMetaData)

module Convert = struct
  module C = Syntax.Convert (AnnotationMetaData) (ModingMetaData)
  include C

  let typ = C.typ (fun x -> x)
end

(* NOTE: no support for translating attributes (for now) *)
let attribute_handler
    (_: AnnotationPass.Prog.attribute_t list)
  : ModePass.Prog.attribute_t list =
  []

type error_sort_t =
  | OutVarShadowing of id_t
  | IOViolationVar of
      { var: Syntax.Common.member_qualified_name_t
      ; is_out: bool }
  | IOViolationFun of Syntax.Common.module_qualified_name_t
type error_t = {callstack: string list; sort: error_sort_t}
type 'a m = ('a, error_t) Result.t

let soft_error_p: error_t -> bool = function
  | {callstack = _; sort = OutVarShadowing _} -> true
  | {callstack = _; sort = IOViolationVar _} -> true
  | {callstack = _; sort = IOViolationFun _} -> true

let on_error_push_callstack (loc: string) (comp: 'a m): 'a m =
  Result.map_error
    (fun err -> { err with callstack = loc :: err.callstack })
    comp

open struct
  let ( let* ) = Result.bind
end

module Util = struct
  type partition_args_by_modes_t =
    | PositionalPartition of
        { args_in:  AnnotationPass.Prog.expr_t list
        ; args_out: AnnotationPass.Prog.expr_t list }
    | Unknown

  (** The additional `bool` return is for whether named args are used. These are
      not supported, so their presence means we should generate a stub.
  *)
  let partition_args_by_modes
      (args: AnnotationPass.Prog.arglist_t) (anns: Annotation.mode_t list option)
    : partition_args_by_modes_t * bool =
    let named_args_p = List.length args.named <> 0 in
    (* NOTE: The annotation pass assures us that the mode list has the same
       length as the argument list *)
    let ( let< ) = Option.bind in
    let res = begin
      let< anns = anns in
      let anns' = begin
        if not named_args_p then anns
        else List.(take (length args.positional) anns)
      end in
      let args_with_anns =
        List.map2 (fun arg mode -> (arg, mode)) args.positional anns' in
      let (in_args, out_args) =
        List.partition_map
          (function (arg, mode) ->
             if mode = Annotation.Input
             then Either.left arg
             else Either.right arg)
          args_with_anns
      in
      Option.Some
        (PositionalPartition
           {args_in = in_args; args_out = out_args})
    end in
    ( Option.fold ~none:Unknown ~some:(fun x -> x) res
    , named_args_p)

  let id_in_formals
      (id: id_t) (ps: AnnotationPass.TopDecl.formal_t list)
    : bool =
    List.exists (function AnnotationPass.TopDecl.Formal (p_id, _) -> id = p_id) ps
end

let rec mode_expr_no_out_vars_extended_pattern
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (pat: AnnotationPass.Prog.extended_pattern_t)
  : ModePass.Prog.extended_pattern_t m =
  let here = "Moder.mode_expr_no_out_vars_extended_pattern" in
  match pat with
  | EPatLit l ->
    Result.Ok ModePass.Prog.(
      EPatLit l)
  | EPatVar (pv_id, opt_tp) ->
    let* () =
      Result.error_when (Util.id_in_formals pv_id vars_out)
      begin
        { callstack = [here]
        ; sort = OutVarShadowing pv_id }
      end
    in
    let opt_tp' = Option.map Convert.typ opt_tp in
    Result.Ok
      ModePass.Prog.(
        EPatVar (pv_id, opt_tp'))
  | EPatCtor (c_id_opt, pats) ->
    (* NOTE: we assume construct ids are pulled from a distinct namespace from variables.
       TODO: is the above a sound assumption? *)
    let* pats' =
      List.mapMResult
        (mode_expr_no_out_vars_extended_pattern vars_out)
        pats
    in
    Result.Ok ModePass.Prog.(
      EPatCtor (c_id_opt, pats'))

let rec mode_expr_no_out_vars_pattern
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (pat: AnnotationPass.Prog.pattern_t)
  : ModePass.Prog.pattern_t m =
  let here = "Moder.mode_expr_no_out_vars_pattern:" in

  match pat with
  | PatVar (pv_id, tp_opt) ->
    let* () =
      Result.error_when (Util.id_in_formals pv_id vars_out)
        begin
          { callstack = [here]
          ; sort = OutVarShadowing pv_id }
        end
    in
    Result.Ok ModePass.Prog.(
      PatVar (pv_id, Option.map Convert.typ tp_opt))
  | PatCtor (ctor_id, ctor_pats) ->
    let* ctor_pats' =
      List.mapMResult (mode_expr_no_out_vars_pattern vars_out) ctor_pats in
    Result.Ok ModePass.Prog.(
      PatCtor (ctor_id, ctor_pats'))

let rec mode_expr_no_out_vars
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (e: AnnotationPass.Prog.expr_t)
  : ModePass.Prog.expr_t m =
  let here = "Moder.mode_expr_no_out_vars:" in

  match e with
  | Suffixed (e_prefix, suff) ->
    let* e_prefix' = begin
      (* Tracking of member qualifications on outvar IO violations *)
      let err_qualify_member (e: error_t): error_t =
        match (e, suff) with
        | ( { callstack = callstack
            ; sort =
                IOViolationVar {var = var; is_out = is_out} }
          , AugDot (DSId m_id, _) )
          ->
          { callstack = callstack
          ; sort =
              IOViolationVar {var = NonEmptyList.snoc var m_id; is_out = is_out} }
        | _ -> e
      in
      Result.map_error err_qualify_member
        (mode_expr_no_out_vars vars_out e_prefix)
    end in
    let* suff' = mode_expr_no_out_vars_suffix vars_out suff in
    Result.Ok (ModePass.Prog.Suffixed (e_prefix', suff'))

  | NameSeg (seg_id, tp_args) ->
    (* TODO: emit an error if there is name shadowing *)
    let* () =
      Result.error_when (Util.id_in_formals seg_id vars_out)
        begin
          { callstack = [here]
          ; sort = IOViolationVar
                { var = NonEmptyList.singleton seg_id
                ; is_out = true }}
        end in
    let tp_args' = List.map Convert.typ tp_args in
    Result.Ok ModePass.Prog.(
        NameSeg (seg_id, tp_args'))

  | Lambda (ps, body) ->
    let lambda_formal_in_vars_out_p
      : (id_t * AnnotationPass.Type.t option) -> bool = function
      | (id, _) -> Util.id_in_formals id vars_out
    in
    let maybe_formal_in_vars_out =
      List.(find_opt lambda_formal_in_vars_out_p ps) in
    let* () =
      Result.error_when Option.(is_some maybe_formal_in_vars_out)
        begin
          let (id, _) = Option.get maybe_formal_in_vars_out in
          { callstack = [here]
          ; sort = OutVarShadowing id }
        end
    in
    let ps' =
      List.map
        (function (id, tp_opt) -> (id, Option.map Convert.typ tp_opt))
        ps
    in
    let* body' = mode_expr_no_out_vars vars_out body in
    Result.Ok ModePass.Prog.(
      Lambda (ps', body'))

  | MapDisplay kvs ->
    let* kvs' =
      List.mapMResult
        (function (k, v) ->
           let* k' = mode_expr_no_out_vars vars_out k in
           let* v' = mode_expr_no_out_vars vars_out v in
           Result.Ok (k', v'))
        kvs
    in
    Result.Ok ModePass.Prog.(
      MapDisplay kvs')

  | SeqDisplay seq_disp ->
    let* seq_disp' = begin
      match seq_disp with
      | SeqEnumerate es ->
        let* es' = List.mapMResult (mode_expr_no_out_vars vars_out) es in
        Result.Ok ModePass.Prog.(
            SeqEnumerate es')
      | SeqTabulate
          { gen_inst = tp_ps; len = len; func = func } ->
        let tp_ps' = List.map Convert.typ tp_ps in
        let* len'  = mode_expr_no_out_vars vars_out len in
        let* func' = mode_expr_no_out_vars vars_out func in
        Result.Ok ModePass.Prog.(
            SeqTabulate { gen_inst = tp_ps'; len = len'; func = func' })
    end in
    Result.Ok ModePass.Prog.(
      SeqDisplay seq_disp')

  | SetDisplay es ->
    let* es' =
      List.mapMResult (mode_expr_no_out_vars vars_out) es in
    Result.Ok ModePass.Prog.(
        SetDisplay es')

  | If (_, guard, then_, else_) ->
    let* guard' = mode_expr_no_out_vars vars_out guard in
    let* then_' = mode_expr_no_out_vars vars_out then_ in
    let* else_' = mode_expr_no_out_vars vars_out else_ in
    Result.Ok ModePass.Prog.(
      If (None, guard', then_', else_'))

  | Match ((), scrut, branches) ->
    let* scrut' = mode_expr_no_out_vars vars_out scrut in
    let* branches' =
        List.(mapMResult (mode_expr_no_out_vars_case vars_out) branches) in
    Result.Ok ModePass.Prog.(
      Match (None, scrut', branches'))

  | Quantifier ((), e_quant) ->
    let* e_quant' = mode_expr_no_out_vars_quantification vars_out e_quant in
    Result.Ok ModePass.Prog.(
        Quantifier (None, e_quant'))

  | SetComp e_scomp ->
    let* e_scomp_qdom' = mode_expr_no_out_vars_qdom vars_out e_scomp.qdom in
    let* e_scomp_body' =
      Result.map_option (mode_expr_no_out_vars vars_out) e_scomp.body in
    Result.Ok
      (ModePass.Prog.SetComp {qdom = e_scomp_qdom'; body = e_scomp_body'})

  | StmtInExpr (_, e) ->
    (* NOTE: For now, we (silently) drop statements in expressions *)
    (* TODO: Generate something for the user indicating the assert/assume/etc
       was dropped *)
    mode_expr_no_out_vars vars_out e

  | Let {ghost = ghost; pats = pats; defs = defs; body = body} ->
    let* pats' =
      on_error_push_callstack here
        (List.mapMResult
           (mode_expr_no_out_vars_pattern vars_out)
           NonEmptyList.(as_list pats))
    in
    let* defs' =
      List.mapMResult (mode_expr_no_out_vars vars_out)
        (NonEmptyList.as_list defs)
    in
    let* body' = mode_expr_no_out_vars vars_out body in
    Result.Ok
      ModePass.Prog.(
        Let { ghost = ghost; pats = NonEmptyList.coerce pats'
            ; defs = NonEmptyList.coerce defs'
            ; body = body'})

  | MapComp e_mcomp ->
    let* e_mcomp_qdom = mode_expr_no_out_vars_qdom vars_out e_mcomp.qdom in
    let* e_mcomp_key =
      Result.map_option (mode_expr_no_out_vars vars_out) e_mcomp.key in
    let* e_mcomp_valu = mode_expr_no_out_vars vars_out e_mcomp.valu in
    Result.Ok
      (ModePass.Prog.MapComp
         { qdom = e_mcomp_qdom
         ; key = e_mcomp_key
         ; valu = e_mcomp_valu })

  | Lit l ->
    Result.Ok ModePass.Prog.(Lit l)
  | This ->
    failwith (here ^ " `this` not supported (should have been caught earlier!)")
  | Cardinality e ->
    let* e' = mode_expr_no_out_vars vars_out e in
    Result.Ok ModePass.Prog.(Cardinality e')
  | Tuple es ->
    let* es' = List.mapMResult (mode_expr_no_out_vars vars_out) es in
    Result.Ok ModePass.Prog.(
      Tuple es')
  | Unary (uop, e) ->
    let* e' = mode_expr_no_out_vars vars_out e in
    Result.Ok ModePass.Prog.(
      Unary (uop, e'))
  | Binary ((), bop, e1, e2) ->
    let* e1' = mode_expr_no_out_vars vars_out e1 in
    let* e2' = mode_expr_no_out_vars vars_out e2 in
    Result.Ok ModePass.Prog.(
      Binary (None, bop, e1', e2'))
  | Lemma {lem = lem; e = e} ->
    let* lem' = mode_expr_no_out_vars vars_out lem in
    let* e'   = mode_expr_no_out_vars vars_out e in
    Result.Ok ModePass.Prog.(
      Lemma {lem = lem'; e = e'})

and mode_expr_no_out_vars_suffix
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (suff: AnnotationPass.Prog.suffix_t)
  : ModePass.Prog.suffix_t m =
  let here = "Moder.mode_expr_no_out_vars_suffix:" in

  (* NOTE: outvar shadowing doesn't include member names *)
  match suff with
  | AugDot (dotsuffix, tp_args) ->
    let tp_args' = List.map Convert.typ tp_args in
    Result.Ok (ModePass.Prog.AugDot (dotsuffix, tp_args'))
  | DataUpd mem_upds ->
    let* mem_upds' =
      List.mapMResult (function (m_id, new_val) ->
          let* new_val' = mode_expr_no_out_vars vars_out new_val in
          Result.Ok (m_id, new_val'))
        (NonEmptyList.as_list mem_upds)
    in
    Result.Ok
      (ModePass.Prog.DataUpd
         (NonEmptyList.coerce mem_upds'))
  | Subseq {lb = lb; ub = ub} ->
    let* lb' = Result.map_option (mode_expr_no_out_vars vars_out) lb in
    let* ub' = Result.map_option (mode_expr_no_out_vars vars_out) ub in
    Result.Ok
      (ModePass.Prog.Subseq {lb = lb'; ub = ub'})
  | SliceLen {sublens = sublens; to_end = to_end} ->
    let* sublens' =
      List.mapMResult
        (mode_expr_no_out_vars vars_out)
        NonEmptyList.(as_list sublens)
    in
    Result.Ok
      (ModePass.Prog.SliceLen
         { sublens = NonEmptyList.coerce sublens'
         ; to_end = to_end })
  | SeqUpd {idx = idx; v = v} ->
    let* idx' = mode_expr_no_out_vars vars_out idx in
    let* v'   = mode_expr_no_out_vars vars_out v in
    Result.Ok
      (ModePass.Prog.SeqUpd {idx = idx'; v = v'})
  | Sel e_sel ->
    let* e_sel' = mode_expr_no_out_vars vars_out e_sel in
    Result.Ok
      (ModePass.Prog.Sel e_sel')
  | ArgList (args, ann) ->
    (* If no output variables are allowed, no predicates marked for
       functionalization are allowed either *)
    let functionalize_p =
      Option.fold ~none:false
        ~some:(function (_, arg_modes) ->
            List.exists ((=) Syntax.Annotation.Output) arg_modes)
        ann
    in
    let* () =
      Result.error_when functionalize_p begin
        { callstack = [here]
        ; sort =
            IOViolationFun Option.(let (mq_id, _) = get ann in mq_id) }
      end
    in
    let* args_pos' =
      List.mapMResult (mode_expr_no_out_vars vars_out) args.positional in
    let* args_nam' =
      List.mapMResult
        (function (id, expr) ->
           let* expr' = mode_expr_no_out_vars vars_out expr in
           Result.Ok (id, expr'))
        args.named in
    Result.Ok
      (ModePass.Prog.ArgList
         ( {positional = args_pos'; named = args_nam'}
         , None ))

and mode_expr_no_out_vars_case
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (b: AnnotationPass.Prog.case_expr_t)
  : ModePass.Prog.case_expr_t m =
  let Case (attrs, e_pat, body) = b in
  let* e_pat' = mode_expr_no_out_vars_extended_pattern vars_out e_pat in
  let* body'  = mode_expr_no_out_vars vars_out body in
  Result.Ok ModePass.Prog.(
    Case (attribute_handler attrs, e_pat', body'))

and mode_expr_no_out_vars_quantification
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (q: AnnotationPass.Prog.quantification_t)
  : ModePass.Prog.quantification_t m =
  let* qdom'  = mode_expr_no_out_vars_qdom vars_out q.qdom in
  let* qbody' = mode_expr_no_out_vars vars_out q.qbody in
  Result.Ok ModePass.Prog.(
    {qt = q.qt; qdom = qdom'; qbody = qbody'})

and mode_expr_no_out_vars_qdom
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (qdom: AnnotationPass.Prog.qdom_t)
  : ModePass.Prog.qdom_t m =
  let here = "Moder.mode_expr_no_out_vars_qdom:" in

  let aux_qvar_decl (qvar: AnnotationPass.Prog.qvar_decl_t)
    : ModePass.Prog.qvar_decl_t m =
    let QVar (q_id, tp_opt, dom_col, attrs) = qvar in
    let* () =
      Result.error_when (Util.id_in_formals q_id vars_out)
        begin
          { callstack = [here]
          ; sort = OutVarShadowing q_id }
        end
    in
    let tp_opt' = Option.map Convert.typ tp_opt in
    let* dom_col' =
      Result.map_option (mode_expr_no_out_vars vars_out) dom_col in
    let attrs' = attribute_handler attrs in
    Result.Ok ModePass.Prog.(
        QVar (q_id, tp_opt', dom_col', attrs'))
  in

  let QDom {qvars = qvars; qrange = qrange} = qdom in
  let* qvars' = List.mapMResult aux_qvar_decl qvars in
  let* qrange' =
    Result.map_option (mode_expr_no_out_vars vars_out) qrange in
  Result.Ok ModePass.Prog.(
      QDom {qvars = qvars'; qrange = qrange'})

(* let mode_expr_conjunct_funcall *)
(*     (vars_in:  AnnotationPass.TopDecl.formal_t list) *)
(*     (vars_out: AnnotationPass.TopDecl.formal_t list) *)
(*     (args: AnnotationPass.Prog.arglist_t) *)
(*     (ann: AnnotationMetaData.arglist_t) *)
(*   : ModePass.Prog.expr_t m = *)
(*   let (pos_args_in, pos_args_out, named_args_p) = begin *)
(*     let (part, named) = *)
(*       Util.partition_args_by_modes args *)
(*         (Option.map (function (_, modes) -> modes) ann) *)
(*     in *)
(*     let (pos_args_in, pos_args_out) = begin *)
(*       match part with *)
(*       | PositionalPartition {args_in = args_in; args_out = args_out} -> *)
(*         (args_in, args_out) *)
(*       | Unknown -> *)
(*         (\* NOTE: calls without annotations are assumed to be all input-moded *\) *)
(*         (args.positional, []) *)
(*     end in *)
(*     (pos_args_in, pos_args_out, named) *)
(*   end in *)
(*   (\* TODO: *)
(*      1. check input arguments don't contain output variables *)

(*         NOTE: identifiers not declared in the formal parameter list are assumed *)
(*         to be input-moded (local variables, constructors) *)

(*      2. check output arguments are member-qualified output variables, and *)
(*         possibly including length *)

(*      3. if there are any named arguments, indicate that a stub should be generated *\) *)
(*   let* _ = *)
(*     if named_args_p then make_stub () *)
(*     else return () *)
(*   in *)
(*   foo1 *)

(* let mode_expr_conjunct *)
(*     (vars_in:  AnnotationPass.TopDecl.formal_t list) *)
(*     (vars_out: AnnotationPass.TopDecl.formal_t list) *)
(*     (e: AnnotationPass.Prog.expr_t) *)
(*   : ModePass.Prog.expr_t m = *)
(*   match e with *)
(*   | Suffixed (e_callee, suff) -> begin *)
(*       match suff with *)
(*       | ArgList (args, anns) -> *)
(*         let (pos_args_in, pos_args_out, named_args_p) = begin *)
(*           let (part, named) = *)
(*             Util.partition_args_by_modes args *)
(*               (Option.map (function (_, modes) -> modes) anns) *)
(*           in *)
(*           let (pos_args_in, pos_args_out) = begin *)
(*             match part with *)
(*             | PositionalPartition {args_in = args_in; args_out = args_out} -> *)
(*               (args_in, args_out) *)
(*             | Unknown -> *)
(*               (\* NOTE: calls without annotations are assumed to be all input-moded *\) *)
(*               (args.positional, []) *)
(*           end in *)
(*           (pos_args_in, pos_args_out, named) *)
(*         end in *)
(*         foo1 *)
(*       | _ -> foo01 *)
(*     end *)
(*   | _ -> foo1 *)
