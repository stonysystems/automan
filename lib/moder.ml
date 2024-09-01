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
    ; out_vars: outvar_lhs_t list }
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

  (* pass-through conversion (no interesting annotations added here, just to get
     the types right) *)
  let expr (_e: AnnotationPass.Prog.expr_t): ModePass.Prog.expr_t =
    failwith "Moder.Convert.expr: TODO"
end

module Erase = struct
  module Annotations = struct
    module E = Syntax.Erase (AnnotationMetaData)
    include E
  end
  module Modings = struct
    module E = Syntax.Erase (ModingMetaData)
    include E
  end
end

(* NOTE: no support for translating attributes (for now) *)
let attribute_handler
    (_: AnnotationPass.Prog.attribute_t list)
  : ModePass.Prog.attribute_t list =
  []

(* type error_sort_t = *)
(*   | OutVarShadowing of id_t *)
(*   | IOViolationVar of *)
(*       { var: Syntax.Common.member_qualified_name_t *)
(*       ; is_out: bool } *)
(*   | IOViolationFun of Syntax.Common.module_qualified_name_t *)
(*   | IllegalOutVarLHS of AnnotationPass.Prog.expr_t *)
(*   | UnsupportedNamedArgs of Syntax.Common.module_qualified_name_t *)
(*   | UnsupportedTypeArgs of AnnotationPass.Prog.expr_t *)
type 'e error_t = {callstack: string list; sort: 'e}
type ('a, 'e) m = ('a, 'e error_t) Result.t

let on_error_push_callstack (loc: string) (comp: ('a, 'e) m): ('a, 'e) m =
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

  (** The additional `bool` return is for whether named args are used. These are
      not supported, so their presence means we should generate a stub.
  *)
  let partition_args_by_modes
      (args: AnnotationPass.Prog.arglist_t) (anns: Annotation.mode_t list)
    : partition_args_by_modes_t * bool =
    let named_args_p = List.length args.named <> 0 in
    (* NOTE: The annotation pass ensures that the mode list has the same
       length as the argument list *)
    let anns' = begin
      if not named_args_p then anns
      else List.(take (length args.positional) anns)
    end in
    let args_with_anns =
      List.map2 (fun arg mode -> (arg, mode)) args.positional anns' in
    let (in_args, out_args) =
      List.partition_map
        (function
          | (arg, Annotation.Input)  -> Either.left arg
          | (arg, Annotation.Output) -> Either.right arg)
        args_with_anns
    in
    ( PositionalPartition {args_in = in_args; args_out = out_args}
    , named_args_p )

  let id_in_formals
      (id: id_t) (ps: AnnotationPass.TopDecl.formal_t list)
    : bool =
    List.exists (function AnnotationPass.TopDecl.Formal (p_id, _) -> id = p_id) ps

  (* NOTE: change this when other "members" are allowed (digits, sequence/key
     selections) *)
  let outvar_lhs_qualify
      (out_var: Definitions.outvar_lhs_t)
      (mem: (id_t, Definitions.unary_op_for_outvar_t) Either.t)
      (err: 'e)
    : (Definitions.outvar_lhs_t, 'e) Result.t =
    Option.fold
      ~none:begin
        Result.Ok begin
          match mem with
          | Either.Left id ->
            { out_var
              with mq_outvar =
                     NonEmptyList.snoc out_var.mq_outvar id }
          | Either.Right uop ->
            { out_var with uop = Some uop }
        end
      end
      ~some:(fun _ -> Result.Error err)
      out_var.uop

  let outvar_lhs_to_expr (var: Definitions.outvar_lhs_t): ParserPass.Prog.expr_t =
    let e = ParserPass.Prog.from_qualified_id var.mq_outvar in
    match var.uop with
    | None -> e
    | Some Definitions.Cardinality ->
      ParserPass.Prog.Cardinality e

end

(* Checks whether the given expression is a legal LHS for an assignment to an
   output-moded variable *)
type error_mode_expr_outvar_lhs_t =
   | IllegalOutVarLHS of ParserPass.Prog.expr_t
   | UnsupportedTypeArgs of Definitions.outvar_lhs_t

(**
   Input:
   - `vars_out`: the set of output-moded variables
   - `e`: the expression to check
   Output:
    - `Result.Ok` means the expression is a legal output-variable LHS (evidenced
      by the value)
    - `Result.Error` means the expression is not a legal output-variable LHS
*)
let mode_expr_outvar_lhs
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (e: AnnotationPass.Prog.expr_t)
  : (Definitions.outvar_lhs_t, error_mode_expr_outvar_lhs_t) m =
  let here = "Moder.mode_expr_outvar_lhs" in

  let rec aux_expr
      (e: AnnotationPass.Prog.expr_t)
    : (Definitions.outvar_lhs_t, error_mode_expr_outvar_lhs_t) Result.t =
    match e with
    | Suffixed (pref, suff) ->
      let* pref' = aux_expr pref in
      aux_suffix pref' suff

    | NameSeg (id, tp_args) ->
      (* 2.1 id must be an outvar *)
      let* () =
        Result.error_when
          (not (Util.id_in_formals id vars_out))
          (IllegalOutVarLHS (Erase.Annotations.expr e))
      in
      let ov = Definitions.(
          { mq_outvar = NonEmptyList.singleton id
          ; uop = None })
      in
      (* 2.2 type arguments not supported *)
      let* () =
        Result.error_when (List.length tp_args <> 0)
          (UnsupportedTypeArgs ov)
      in
      Result.Ok ov

    | StmtInExpr (_, e') ->
      (* 3.0 We drop statements in expressionsl (e.g., reveal/assume/assert) *)
      aux_expr e'

    | Cardinality e as e_orig ->
      let* e' = aux_expr e in
      Util.outvar_lhs_qualify
        e' (Either.Right Definitions.Cardinality)
        (IllegalOutVarLHS (Erase.Annotations.expr e_orig))

    | Tuple _ ->
      (* TODO: consider patterns of outvars *)
      Result.Error (IllegalOutVarLHS (Erase.Annotations.expr e))

    | Lemma {lem = _; e = body} ->
      (* NOTE: we drop lemma invocations *)
      aux_expr body

    | Lambda _
    | MapDisplay _
    | SeqDisplay _
    | SetDisplay _
    | If (_, _, _, _)
    | Match (_, _, _)
    | Quantifier (_, _)
    | SetComp _
    | Let _
    | MapComp _
    | Lit _
    | This
    | Unary (_, _)
    | Binary (_, _, _, _) ->
      Result.Error (IllegalOutVarLHS (Erase.Annotations.expr e))

  and aux_suffix
      (pref: Definitions.outvar_lhs_t)
      (suff: AnnotationPass.Prog.suffix_t)
    : (Definitions.outvar_lhs_t, error_mode_expr_outvar_lhs_t) Result.t =
    let e_orig_lazy (_: unit) =
      ParserPass.Prog.Suffixed
        ( Util.outvar_lhs_to_expr pref
        , Erase.Annotations.suffix suff )
    in
    match suff with
    | AugDot (DSId id, tp_args) ->
      let* ov =
        Util.outvar_lhs_qualify pref (Either.Left id)
          (IllegalOutVarLHS
             (ParserPass.Prog.Suffixed
                ( Util.outvar_lhs_to_expr pref
                , AugDot (DSId id, []))))
      in
      let* () =
        Result.error_when
          (List.length tp_args <> 0)
          (UnsupportedTypeArgs ov)
      in
      Result.Ok ov

    | AugDot _
    (* TODO: support members with digit identifiers *)
    | DataUpd _
    (* TODO: consider whether/how to support data updates on output-moded variables *)
    | Subseq _
    (* TODO: could be supported *)
    | SliceLen _
    | SeqUpd _
    (* TODO: consider whether/how to support subsequences on output-moded variables *)
    | Sel _
    (* TODO: consider whether/how to support selection on output-moded variables *)
    | ArgList (_, _) ->
      Result.Error (IllegalOutVarLHS (e_orig_lazy()))

  in
  Result.map_error
    (fun e -> {callstack = [here]; sort = e})
    (aux_expr e)

type error_mode_expr_no_out_vars_t =
  | OutVarOccur of
      { occuring_outvar: id_t
      ; shadowed: bool }
  | FunctionalizedPredOccur of Syntax.Common.module_qualified_name_t

let mode_expr_no_out_vars
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (e: AnnotationPass.Prog.expr_t)
  : (ModePass.Prog.expr_t, error_mode_expr_no_out_vars_t) m =
  let here = "Moder.mode_expr_no_out_vars:" in

  let rec aux_expr = function
    | AnnotationPass.Prog.Suffixed (pref, suff) ->
      let* pref' = aux_expr pref in
      let* suff' = aux_suffix suff in
      Result.Ok (ModePass.Prog.Suffixed (pref', suff'))

    | NameSeg (seg_id, seg_tp_args) ->
      let* () =
        Result.error_when (Util.id_in_formals seg_id vars_out)
          { callstack = [here]
          ; sort = OutVarOccur {occuring_outvar = seg_id; shadowed = false} }
      in
      let seg_tp_args' = List.map Convert.typ seg_tp_args in
      Result.Ok
        (ModePass.Prog.NameSeg (seg_id, seg_tp_args'))

    | Lambda (lam_ps, lam_body) ->
      let* lam_ps' =
        List.mapMResult
          begin function (p_id, p_tp_opt) ->
            let* () =
              Result.error_when (Util.id_in_formals p_id vars_out)
                { callstack = [here]
                ; sort = OutVarOccur {occuring_outvar = p_id; shadowed = true} }
            in
            Result.Ok (p_id, Option.map Convert.typ p_tp_opt)
          end
          lam_ps
      in
      let* lam_body' = aux_expr lam_body in
      Result.Ok (ModePass.Prog.Lambda (lam_ps', lam_body'))

    | MapDisplay kvs ->
      let* kvs' =
        List.mapMResult
          begin function (k, v) ->
            let* k' = aux_expr k in
            let* v' = aux_expr v in
            Result.Ok (k', v')
          end
          kvs
      in
      Result.Ok (ModePass.Prog.MapDisplay kvs')

    | SeqDisplay seqd ->
      let* seqd' = begin
        match seqd with
        | SeqEnumerate seqd_enum ->
          let* seqd_enum' = List.mapMResult aux_expr seqd_enum in
          Result.Ok (ModePass.Prog.SeqEnumerate seqd_enum')
        | SeqTabulate seqd_tab ->
          let tp_args' = List.map Convert.typ seqd_tab.gen_inst in
          let* len' = aux_expr seqd_tab.len in
          let* func' = aux_expr seqd_tab.func in
          Result.Ok
            (ModePass.Prog.SeqTabulate
               { gen_inst = tp_args'
               ; len = len'
               ; func = func' })
      end in
      Result.Ok (ModePass.Prog.SeqDisplay seqd')

    | SetDisplay setd ->
      let* setd' = List.mapMResult aux_expr setd in
      Result.Ok (ModePass.Prog.SetDisplay setd')

    | If (_, g, t, e) ->
      let* g' = aux_expr g in
      let* t' = aux_expr t in
      let* e' = aux_expr e in
      Result.Ok (ModePass.Prog.If (None, g', t', e'))

    | Match (_, scrut, branches) ->
      let* scrut' = aux_expr scrut in
      let* branches' =
        List.mapMResult begin function
          | AnnotationPass.Prog.Case (_attrs, e_pat, body) ->
            let attrs' = [] in
            let* e_pat' = aux_extended_pattern e_pat in
            let* body' = aux_expr body in
            Result.Ok (ModePass.Prog.Case (attrs', e_pat', body'))
        end branches
      in
      Result.Ok (ModePass.Prog.Match (None, scrut', branches'))

    | Quantifier (_, qt) ->
      let* qdom' = aux_quantifier_domain qt.qdom in
      let* qbody' = aux_expr qt.qbody in
      Result.Ok ModePass.Prog.(
          Quantifier (None, {qt = qt.qt; qdom = qdom'; qbody = qbody'}))

    | SetComp setc ->
      let* setc_qdom' = aux_quantifier_domain setc.qdom in
      let* setc_body' = Result.map_option aux_expr setc.body in
      Result.Ok (ModePass.Prog.SetComp {qdom = setc_qdom'; body = setc_body'})

    | StmtInExpr (_, e) ->
    (* NOTE: For now, we (silently) drop statements in expressions TODO:
       Generate something for the user indicating that the
       assert/assume/reveal/etc was dropped *)
      aux_expr e

    | Let {ghost = ghost; pats = pats; defs = defs; body = body} ->
      let* pats' =
        Result.map NonEmptyList.coerce
          (List.mapMResult aux_pattern
             (NonEmptyList.as_list pats))
      in
      let* defs' =
        Result.map NonEmptyList.coerce
          (List.mapMResult aux_expr (NonEmptyList.as_list defs)) in
      let* body' = aux_expr body in
      Result.Ok (ModePass.Prog.(
          Let {ghost = ghost; pats = pats'; defs = defs'; body = body'}))

    | MapComp mapc ->
      let* mapc_qdom' = aux_quantifier_domain mapc.qdom in
      let* mapc_key' = Result.map_option aux_expr mapc.key in
      let* mapc_valu' = aux_expr mapc.valu in
      Result.Ok
        (ModePass.Prog.MapComp
           { qdom = mapc_qdom'
           ; key = mapc_key'
           ; valu = mapc_valu' })

    | Lit l ->
      Result.Ok (ModePass.Prog.Lit l)

    | This ->
      failwith (here ^ " `this` not supported (should have been caught earlier!)")

    | Cardinality e ->
      let* e' = aux_expr e in
      Result.Ok (ModePass.Prog.Cardinality e')
    | Tuple es ->
      let* es' = List.mapMResult aux_expr es in
      Result.Ok (ModePass.Prog.Tuple es')

    | Unary (uop, e) ->
      let* e' = aux_expr e in
      Result.Ok (ModePass.Prog.Unary (uop, e'))

    | Binary (_, bop, e1, e2) ->
      let* e1' = aux_expr e1 in
      let* e2' = aux_expr e2 in
      Result.Ok (ModePass.Prog.Binary (None, bop, e1', e2'))

    | Lemma {lem = lem; e = e} ->
      let* lem' = aux_expr lem in
      let* e' = aux_expr e in
      Result.Ok (ModePass.Prog.Lemma {lem = lem'; e = e'})

  and aux_suffix = function
    | AnnotationPass.Prog.AugDot (suff, tp_args) ->
      let tp_args' = List.map Convert.typ tp_args in
      Result.Ok (ModePass.Prog.AugDot (suff, tp_args'))

    | DataUpd dataupd ->
      let* dataupd' =
        Result.map NonEmptyList.coerce
          begin
            List.mapMResult (function (m_id, new_val) ->
                let* new_val' = aux_expr new_val in
                Result.Ok (m_id, new_val'))
              (NonEmptyList.as_list dataupd)
          end
      in
      Result.Ok (ModePass.Prog.DataUpd dataupd')
    | Subseq {lb = lb; ub = ub} ->
      let* lb' = Result.map_option aux_expr lb in
      let* ub' = Result.map_option aux_expr ub in
      Result.Ok (ModePass.Prog.Subseq {lb = lb'; ub = ub'})

    | SliceLen {sublens = sublens; to_end = to_end} ->
      let* sublens' =
        Result.map NonEmptyList.coerce
          (List.mapMResult aux_expr (NonEmptyList.as_list sublens)) in
      Result.Ok (ModePass.Prog.SliceLen {sublens = sublens'; to_end = to_end})
    | SeqUpd {idx = idx; v = v} ->
      let* idx' = aux_expr idx in
      let* v' = aux_expr v in
      Result.Ok (ModePass.Prog.SeqUpd {idx = idx'; v = v'})
    | Sel e ->
      let* e' = aux_expr e in
      Result.Ok (ModePass.Prog.Sel e')
    | ArgList (args, ann) ->
      (* NOTE: If no output variables are allowed, no predicates marked for
         functionalization are allowed either *)
      let exists_output = List.exists ((=) Syntax.Annotation.Output) in
      let* () =
        Option.fold ~none:(Result.Ok ())
          ~some:(function (p_id, arg_modes) ->
            Result.error_when (exists_output arg_modes)
              { callstack = [here]
              ; sort = FunctionalizedPredOccur p_id })
          ann
      in
      let* args_pos' =
        List.mapMResult aux_expr args.positional in
      let* args_nam' =
        List.mapMResult
          begin function (id, arg) ->
            let* arg' = aux_expr arg in
            Result.Ok (id, arg')
          end
          args.named in
      (* NOTE: We delete the annotation here if all arguments are marked input.
         TODO: This /needs/ changing if we support other user annotations (e.g.,
         name for functionalized code) *)
      Result.Ok
        (ModePass.Prog.ArgList
           ({ positional = args_pos'
            ; named = args_nam' }
           ,None))

  and aux_extended_pattern = function
    | AnnotationPass.Prog.EPatLit l ->
      Result.Ok (ModePass.Prog.EPatLit l)
    | EPatVar (pv_id, pv_tp_opt) ->
      let* () =
        Result.error_when (Util.id_in_formals pv_id vars_out)
          { callstack = [here]
          ; sort = OutVarOccur {occuring_outvar = pv_id; shadowed = true} }
      in
      let pv_tp_opt' = Option.map Convert.typ pv_tp_opt in
      Result.Ok (ModePass.Prog.EPatVar (pv_id, pv_tp_opt'))

    | EPatCtor (c_id_opt, e_pats) ->
      let* e_pats' =
        List.mapMResult aux_extended_pattern e_pats in
      Result.Ok (ModePass.Prog.EPatCtor (c_id_opt, e_pats'))

  and aux_quantifier_domain (qdom: AnnotationPass.Prog.qdom_t) =
    let QDom {qvars = qvars; qrange = qrange} = qdom in
    let* qvars' =
      List.mapMResult
        begin function
          | AnnotationPass.Prog.QVar (id, tp, dom_col, _attrs) ->
            let tp' = Option.map Convert.typ tp in
            let* dom_col' = Result.map_option aux_expr dom_col in
            let attrs' = [] in
            Result.Ok (ModePass.Prog.QVar (id, tp', dom_col', attrs'))
        end
        qvars
    in
    let* qrange' = Result.map_option aux_expr qrange in
    Result.Ok (ModePass.Prog.QDom {qvars = qvars'; qrange = qrange'})

  and aux_pattern = function
    | AnnotationPass.Prog.PatVar (pv_id, tp_opt) ->
      let* () =
        Result.error_when (Util.id_in_formals pv_id vars_out)
          { callstack = [here]
          ; sort = OutVarOccur {occuring_outvar = pv_id; shadowed = true} }
      in
      let tp_opt' = Option.map Convert.typ tp_opt in
      Result.Ok (ModePass.Prog.PatVar (pv_id, tp_opt'))
    | PatCtor (c_id, pats) ->
      let* pats' = List.mapMResult aux_pattern pats in
      Result.Ok (ModePass.Prog.PatCtor (c_id, pats'))

  in

  aux_expr e

(* let mode_expr_conjunct_arglist *)
(*     (vars_out: AnnotationPass.TopDecl.formal_t list) *)
(*     (qp_id: Syntax.Common.module_qualified_name_t) *)
(*     (args: AnnotationPass.Prog.arglist_t) (modes: Annotation.mode_t list) *)
(*   : (ModePass.Prog.expr_t * Definitions.outvar_lhs_t list) m = *)
(*   let here = "Moder.mode_expr_conjuct_arglist:" in *)

(*   let (PositionalPartition {args_in = args_in; args_out = args_out}, named_args_p) = *)
(*     Util.partition_args_by_modes args modes in *)
(*   (\* NOTE: We don't support named arguments in our mode analysis *\) *)
(*   let* () = *)
(*     Result.error_when named_args_p begin *)
(*       { callstack = [here] *)
(*       ; sort = UnsupportedNamedArgs qp_id } *)
(*     end *)
(*   in *)
(*   (\* Check that arguments in the input positions contain no output variables, *)
(*      and arguments in output positions are only member-qualified output *)
(*      variables *\) *)
(*   let* (args_in', args_out') = *)
(*     on_error_push_callstack here *)
(*       begin *)
(*         let* args_in' = *)
(*           List.mapMResult (mode_expr_no_out_vars vars_out) args_in in *)
(*         let* args_out' = *)
(*           List.mapMResult (mode_expr_only_out_vars vars_out) args_out in *)
(*         Result.Ok (args_in', args_out') *)
(*       end *)
(*   in *)
(*   let args' = ModePass.Prog.( *)
(*     ArgList *)
(*       ({ positional = *)
(*            List.map Convert.expr args.positional *)
(*        ; named = [] } *)
(*       , Some *)
(*           Definitions.( *)
(*             { callee = qp_id *)
(*             ; in_exprs = List.map Erase.expr args_in' *)
(*             ; out_vars = args_out' }))) *)
(*   in *)
(*   Result.Ok *)
(*     ( ModePass.Prog.( *)
(*           Suffixed(from_qualified_id qp_id, args')) *)
(*     , args_out' ) *)

(* let mode_expr_conjunct_eq *)
(*     (vars_out: AnnotationPass.TopDecl.formal_t list) *)
(*     (e1: AnnotationPass.Prog.expr_t) (e2: AnnotationPass.Prog.expr_t) *)
(*   : (ModePass.Prog.expr_t * Definitions.outvar_lhs_t list) m = *)
(*   (\* 1. see if this determines an output *\) *)
(*   let* ann: Definitions.binary_op_functionalize_eq_t option = *)
(*     begin *)
(*       let* (var_out, is_left) = *)
(*         Result.try_catch *)
(*           (Result.map (fun x -> (x, true)) *)
(*              (mode_expr_only_out_vars vars_out e1)) *)
(*           foo0 *)
(*       in *)
(*       bar *)
(*     end *)
(*   in *)
(*   foo *)

(**
   Input:
   - vars_out: the set of output-moded parameters to the predicate
   - e_conj: the conjuct to annotate
   Output: (e_conj', vars), where
   - e_conj': e_conj with ModePass annotations
   - vars: the (member-qualified) output variables e_conj determines
       if this is [], the expression is purely a requirement on inputs
*)
(* let mode_expr_conjunct *)
(*     (vars_out: AnnotationPass.TopDecl.formal_t list) *)
(*     (e_conj: AnnotationPass.Prog.expr_t) *)
(*   : (ModePass.Prog.expr_t * Definitions.outvar_lhs_t list) m = *)
(*   let here = "Moder.mode_expr_conjunct:" in *)

(*   match e_conj with *)
(*   | Binary ((), bop, e1, e2) -> *)
(*     begin *)
(*       match bop with *)
(*       (\* Type errors *\) *)
(*       | Mul | Div | Mod | Add | Sub -> *)
(*         failwith *)
(*           (here *)
(*            ^ " invalid binary op (expected boolean, fatal): " *)
(*            ^ Common.show_bop_t bop) *)
(*       | _ -> *)
(*         foo_bop *)
(*     end *)
(*   | Suffixed (pref, suff) -> *)
(*     foo_suffixed *)
(*   | NameSeg seg -> *)
(*     foo_nameseg *)
(*   | Lambda (ps, body) -> *)
(*     foo_lambda *)
(*   | MapDisplay kvs -> *)
(*     foo_mapdisplay *)
(*   | SeqDisplay sdisp -> *)
(*     foo_seqdisplay *)
(*   | SetDisplay elems -> *)
(*     foo_setdisplay *)
(*   | If (ann, g, t, e) -> *)
(*     foo_if *)
(*   | Match (ann, scrut, branches) -> *)
(*     foo_match *)
(*   | Quantifier (q, b) -> *)
(*     foo_quantifier *)
(*   | SetComp scomp -> *)
(*     foo_setcomp *)
(*   | StmtInExpr (st, e) -> *)
(*     foo_stmtinexpr *)
(*   | Let l -> *)
(*     foo_let *)
(*   | MapComp mcomp -> *)
(*     foo_mcomp *)
(*   | Lit l -> *)
(*     foo_lit *)
(*   | This -> *)
(*     foo_this *)
(*   | Cardinality exp -> *)
(*     foo_cardinality *)
(*   | Tuple comps -> *)
(*     foo_tuple *)
(*   | Unary (uop, e) -> *)
(*     foo_unary *)
(*   | Lemma {lem = lem; e = e} -> *)
(*     foo_lemma *)

(* let mode_expr_conjunct *)
(*     (vars_out: AnnotationPass.TopDecl.formal_t list) *)
(*     (e_con: AnnotationPass.Prog.expr_t) *)
(*   : (ModePass.Prog.expr_t * Definitions.outvar_lhs_t list) m = *)
(*   match e_con with *)
(*   | Suffixed (e_prefix, e_suff) -> *)
(*     begin *)
(*       (\* 1. check if this is an argument list suffix attached to a predicate *)
(*          marked for functionalization *\) *)
(*       match e_suff with *)
(*       | ArgList (args, Some (qp_id, modes)) -> *)
(*         foo0 *)
(*       | _ -> *)
(*         foo1 *)
(*     end *)
(*   | _ -> foo *)
