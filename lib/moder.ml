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
  type outvar_lhs_fieldlike_t =
    | Cardinality
    | Sel of id_t
  [@@deriving show, eq]

  (** The LHS of assignments to (members of) out vars. Some operations (for
      now, only cardinality) can be treated as pseudo-members that we will try
      to support
  *)
  type outvar_lhs_t =
    { mq_outvar: Common.member_qualified_name_t
    ; fieldlike: outvar_lhs_fieldlike_t option }
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
        (* ; requires: AnnotationPass.Prog.expr_t list  *) }
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
  type quantification_functionalize_var_range_sort_t =
    | QFVarRangeBounds             (* 0 <= qv_id < |outvar|, outvar.fieldlike = Some Cardinality *)
    | QFVarRangeColl               (* qv_id in outvar, outvar.fieldlike = None *)
  [@@deriving show, eq]

  type quantification_functionalize_var_range_t =
    { id: id_t
    ; tp: AnnotationPass.Type.t option
    ; domain: quantification_functionalize_var_range_sort_t * outvar_lhs_t }
  [@@deriving show, eq]

  type quantification_functionalize_var_t =
    | QFVarRange of quantification_functionalize_var_range_t
    | QFVarDom of outvar_lhs_t
  [@@deriving show, eq]

  type quantification_functionalize_t =
    { qvar: quantification_functionalize_var_t
    ; body_outvars: outvar_lhs_t list }
  [@@deriving show, eq]

  (** - outvar_is_left: true iff the (member-qualified) outvar is the left
        expression of the equation
      - outvar: the outvar in the equation
  *)
  type binary_op_functionalize_eq_t =
    { outvar_is_left: bool
    ; outvar: outvar_lhs_t
    ; unassigned_members: Common.member_qualified_name_t list option
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

  type dataupdate_functionalize_t =
    DataUpdUnassigned of outvar_lhs_t list
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
  with type dataupdate_t = Definitions.dataupdate_functionalize_t option
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
  type dataupdate_t = Definitions.dataupdate_functionalize_t option
  [@@deriving show, eq]
end

module ModePass = AST (ModingMetaData)

module Convert = struct
  module C = Syntax.Convert (AnnotationMetaData) (ModingMetaData)
  include C

  let typ = C.typ Fun.id
  let pattern = C.pattern Fun.id
  let extended_pattern = C.extended_pattern Fun.id
  let lambda_params = C.lambda_params Fun.id

  (* pass-through conversion (no interesting annotations added here; this just *)
  (*    exists to make the typechecker happy) *)
  let rec expr (e: AnnotationPass.Prog.expr_t): ModePass.Prog.expr_t =
    let aux_suffix (s: AnnotationPass.Prog.suffix_t): ModePass.Prog.suffix_t =
      match s with
      | AugDot (mem, tps) ->
        AugDot (mem, List.map typ tps)
      | DataUpd ((), mem_upd) ->
        DataUpd
          ( None
          , NonEmptyList.map
              (function (mem, newval) -> (mem, expr newval))
              mem_upd )
      | Subseq {lb = lb; ub = ub} ->
        Subseq {lb = Option.map expr lb; ub = Option.map expr ub}
      | SliceLen {sublens = sublens; to_end = to_end} ->
        SliceLen
          { sublens = NonEmptyList.map expr sublens
          ; to_end = to_end }
      | SeqUpd {idx = idx; v = v} ->
        SeqUpd
          { idx = expr idx
          ; v = expr v }
      | Sel sel ->
        Sel (expr sel)
      | ArgList ({positional = pos; named = nam}, _) ->
        ArgList
          ({ positional = List.map expr pos
           ; named = List.map (function (id, e) -> (id, expr e)) nam }
          , None )              (* TODO: reconsider? as in, should this be forbidden? *)
    in

    let aux_qdom (qdom: AnnotationPass.Prog.qdom_t): ModePass.Prog.qdom_t =
      let QDom {qvars = qvars; qrange = qrange} = qdom in
      let qvars' =
        List.map
          begin function
            | AnnotationPass.Prog.QVar (qv_id, qv_tp, qv_coll, _attrs) ->
              let qv_tp' = Option.map typ qv_tp in
              let qv_coll' = Option.map expr qv_coll in
              ModePass.Prog.QVar (qv_id, qv_tp', qv_coll', [])
          end
          qvars
      in
      let qrange' = Option.map expr qrange in
      QDom {qvars = qvars'; qrange = qrange'}
    in

    match e with
    | Suffixed (pref, suf) ->
      Suffixed (expr pref, aux_suffix suf)
    | NameSeg (id, tps) ->
      ModePass.Prog.NameSeg (id, List.map typ tps)
    | Lambda (ps, body) ->
      let ps' = lambda_params ps in
      let body' = expr body in
      Lambda (ps', body')
    | MapDisplay kvs ->
      MapDisplay (List.map (function (k, v) -> (expr k, expr v)) kvs)
    | SeqDisplay sd ->
        SeqDisplay begin
          match sd with
          | SeqEnumerate es ->
            SeqEnumerate (List.map expr es)
          | SeqTabulate {gen_inst = tp_args; len = len; func = func} ->
            SeqTabulate
              { gen_inst = List.map typ tp_args
              ; len = expr len
              ; func = expr func }
        end
    | SetDisplay es ->
      SetDisplay (List.map expr es)
    | If ((), guard, then_, else_) ->
      If (None, expr guard, expr then_, expr else_)
    | Match ((), scrut, tree) ->
      let scrut' = expr scrut in
      let tree' =
        List.map
          (function
            | AnnotationPass.Prog.Case (_attrs, epats, body) ->
              ModePass.Prog.Case ([], extended_pattern epats, expr body))
          tree
      in
      Match (None, scrut', tree')
    | Quantifier ((), {qt = qt; qdom = qdom; qbody = qbody}) ->
      let qdom' = aux_qdom qdom in
      let qbody' = expr qbody in
      Quantifier (None, {qt = qt; qdom = qdom'; qbody = qbody'})
    | SetComp {qdom = qdom; body = body} ->
      SetComp
        { qdom = aux_qdom qdom
        ; body = Option.map expr body }
    | StmtInExpr (_, _) ->
      failwith "Moder.Convert.expr: TODO statement-in-expression"
    | Let {ghost = g; pats = p; defs = d; body = b} ->
      Let
        { ghost = g
        ; pats = NonEmptyList.map pattern p
        ; defs = NonEmptyList.map expr d
        ; body = expr b}
    | MapComp {imap = imap; qdom = qdom; key = key; valu = valu} ->
      MapComp
        { imap = imap
        ; qdom = aux_qdom qdom
        ; key = Option.map expr key
        ; valu = expr valu }
    | Lit l -> Lit l
    | This -> This
    | Cardinality e ->
      Cardinality (expr e)
    | Tuple es ->
      Tuple (List.map expr es)
    | Unary (uop, e) ->
      Unary (uop, expr e)
    | Binary ((), bop, e1, e2) ->
      Binary (None, bop, expr e1, expr e2)
    | Lemma {lem = lem; e = e} ->
      Lemma
        { lem = expr lem
        ; e = expr e }
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

type 'e error_t = {callstack: string list; sort: 'e}
[@@deriving show]
type ('a, 'e) m = ('a, 'e error_t) Result.t
[@@deriving show]

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
    List.exists (function AnnotationPass.TopDecl.Formal (_, p_id, _) -> id = p_id) ps

  (* NOTE: change this when other "members" are allowed (digits, sequence/key
     selections) *)
  let outvar_lhs_qualify
      (out_var: Definitions.outvar_lhs_t)
      (mem: (id_t, Definitions.outvar_lhs_fieldlike_t) Either.t)
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
          | Either.Right fieldlike ->
            { out_var with fieldlike = Some fieldlike }
        end
      end
      ~some:(fun _ -> Result.Error err)
      out_var.fieldlike

  let outvar_lhs_to_expr (var: Definitions.outvar_lhs_t): ParserPass.Prog.expr_t =
    let e = ParserPass.Prog.from_qualified_id var.mq_outvar in
    match var.fieldlike with
    | None -> e
    | Some Definitions.Cardinality ->
      ParserPass.Prog.Cardinality e
    | Some Definitions.Sel s ->
      ParserPass.Prog.(Suffixed (e, Sel (NameSeg (s, []))))

  (* FIXME: DRY *)
  let outvar_lhs_to_modepass_expr (var: Definitions.outvar_lhs_t): ModePass.Prog.expr_t =
    let e = ModePass.Prog.from_qualified_id var.mq_outvar in
    match var.fieldlike with
    | None -> e
    | Some Definitions.Cardinality ->
      ModePass.Prog.Cardinality e
    | Some (Definitions.Sel s) ->
      ModePass.Prog.(Suffixed (e, Sel (NameSeg (s, []))))

  let assemble_positional_args_by_modes
      (args_in: ModePass.Prog.expr_t list) (args_out: Definitions.outvar_lhs_t list)
      (anns: Annotation.mode_t list)
    : ModePass.Prog.expr_t list =
    (* <= in consideration of named args *)
    assert List.(length args_in + length args_out <= length anns);
    let rec aux args_in args_out acc = function
      | Annotation.Input :: anns ->
        let (hd, tl) = (List.hd args_in, List.tl args_in) in
        aux tl args_out (hd :: acc) anns
      | Annotation.Output :: anns ->
        let (hd, tl) = (List.hd args_out, List.tl args_out) in
        aux args_in tl (outvar_lhs_to_modepass_expr hd :: acc) anns
      | [] -> acc
    in
    List.rev (aux args_in args_out [] anns)

end

(* Checks whether the given expression is a legal LHS for an assignment to an
   output-moded variable *)
type error_mode_expr_outvar_lhs_t =
   | IllegalOutVarLHS of ParserPass.Prog.expr_t
   | UnsupportedTypeArgs of Definitions.outvar_lhs_t
[@@deriving show]
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
          (lazy (IllegalOutVarLHS (Erase.Annotations.expr e)))
      in
      let ov = Definitions.(
          { mq_outvar = NonEmptyList.singleton id
          ; fieldlike = None })
      in
      (* 2.2 type arguments not supported *)
      let* () =
        Result.error_when (List.length tp_args <> 0)
          (lazy (UnsupportedTypeArgs ov))
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
          (lazy (UnsupportedTypeArgs ov))
      in
      Result.Ok ov
    | Sel (NameSeg (id, tp_args)) ->
      let* ov =
        Util.outvar_lhs_qualify pref (Either.right (Definitions.Sel id))
          (IllegalOutVarLHS
             (ParserPass.Prog.Suffixed
                ( Util.outvar_lhs_to_expr pref
                , Sel (NameSeg (id, [])))))
      in
      let* () =
        Result.error_when
          (List.length tp_args <> 0)
          (lazy (UnsupportedTypeArgs ov))
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

type error_outvar_occur_t =
  { occurring_outvar: id_t
  ; shadowed: bool }
[@@deriving show]

type error_mode_expr_no_out_vars_t =
  | OutVarOccur of error_outvar_occur_t
  | FunctionalizedPredOccur of Syntax.Common.module_qualified_name_t
[@@deriving show]

let rec mode_expr_no_out_vars_extended_pattern
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (epat: AnnotationPass.Prog.extended_pattern_t)
  : (ModePass.Prog.extended_pattern_t, error_outvar_occur_t) m =
  match epat with
  | EPatLit l ->
    Result.Ok (ModePass.Prog.EPatLit l)
  | EPatVar (pv_id, pv_tp_opt) ->
    let* () =
      Result.error_when (Util.id_in_formals pv_id vars_out)
        (lazy
          { callstack = []
          ; sort = {occurring_outvar = pv_id; shadowed = true} })
    in
    let pv_tp_opt' = Option.map Convert.typ pv_tp_opt in
    Result.Ok (ModePass.Prog.EPatVar (pv_id, pv_tp_opt'))

  | EPatCtor (c_id_opt, e_pats) ->
    let* e_pats' =
      List.mapMResult
        (mode_expr_no_out_vars_extended_pattern vars_out)
        e_pats
    in
    Result.Ok (ModePass.Prog.EPatCtor (c_id_opt, e_pats'))

let rec mode_expr_no_out_vars_pattern
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (pat: AnnotationPass.Prog.pattern_t)
  : (ModePass.Prog.pattern_t, error_outvar_occur_t) m =
  let here = "Moder.mode_expr_no_out_vars_pattern" in

  match pat with
  | PatVar (p_id, tp_opt) ->
    let* () =
      Result.error_when (Util.id_in_formals p_id vars_out)
        (lazy
          { callstack = [here]
          ; sort = {occurring_outvar = p_id; shadowed = true }})
    in
    let tp_opt' = Option.map Convert.typ tp_opt in
    Result.Ok (ModePass.Prog.PatVar (p_id, tp_opt'))
  | PatCtor (ctor_id, pats) ->
    let* pats' = List.mapMResult (mode_expr_no_out_vars_pattern vars_out) pats in
    Result.Ok (ModePass.Prog.PatCtor (ctor_id, pats'))

let rec mode_expr_no_out_vars
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    ?(except: Common.member_qualified_name_t option = None) (* functional record update exception *)
    (e: AnnotationPass.Prog.expr_t)
  : ( ModePass.Prog.expr_t * Common.member_qualified_name_t list option
    , error_mode_expr_no_out_vars_t) m =
  let here = "Moder.mode_expr_no_out_vars:" in
  let no_unassigneds = Option.map (Fun.const []) except in

  let aux_suffix
      ~(except: (Common.member_qualified_name_t * Common.member_qualified_name_t list) option)
    = function
      | AnnotationPass.Prog.AugDot (suff, tp_args) ->
        let tp_args' = List.map Convert.typ tp_args in
        Result.Ok (ModePass.Prog.AugDot (suff, tp_args'), no_unassigneds)

      | DataUpd ((), dataupd) -> begin
          match except with
          | None ->
            let* dataupd' =
              NonEmptyList.as_list dataupd
              |> List.mapMResult begin function (m_id, new_val) ->
                let* (new_val', _discard) =
                  mode_expr_no_out_vars vars_out ~except:None new_val in
                Result.Ok (m_id, new_val')
              end
              |> Result.map NonEmptyList.coerce
            in
            Result.Ok
              ( ModePass.Prog.DataUpd (None, dataupd')
              , None )
          | Some (except, unassigneds) ->
            let* (dataupd', unassigneds') =
              NonEmptyList.as_list dataupd
              |> List.fold_left
                (* TODO: This should be factored out for maintainability *)
                begin fun new_upds old_upd ->
                  let (m_id, new_val) = old_upd in
                  let* (new_upds, unassigneds) = new_upds in
                  match Result.to_option (mode_expr_outvar_lhs vars_out new_val) with
                  | None ->
                    (* TODO: for recursive analysis, replace ~except:None with NonEmptyList.snoc except m_id,
                       then replace any occurrence of that in unassigneds with the unassigneds generated from the call *)

                    (* TODO: outvar_lhs_t needs dotsuffix qualifications, we
                       aren't tracking numeric fields yet *)
                    let* (new_val', _) = mode_expr_no_out_vars vars_out ~except:None new_val in
                    let unassigneds' =
                      List.filter
                        (fun ov ->
                           Either.fold m_id
                             ~left:(fun id -> not (ov = NonEmptyList.snoc except id))
                             ~right:(Fun.const false))
                        unassigneds
                    in
                    Result.Ok (new_upds @ [(m_id, new_val')], unassigneds')
                  | Some ov ->
                    let* () =
                      Result.error_when
                        (Either.fold m_id
                           ~left:(fun id ->
                               not
                                 (  ov.mq_outvar = NonEmptyList.snoc except id
                                 && Option.is_none ov.fieldlike ))
                           ~right:(Fun.const true))
                        begin lazy
                          { callstack = [here]
                          ; sort =
                              OutVarOccur
                                { occurring_outvar = NonEmptyList.head except
                                ; shadowed = false }}
                        end
                    in
                    Result.Ok
                      ( new_upds @ [(m_id, Util.outvar_lhs_to_modepass_expr ov)]
                      , unassigneds @
                        if List.exists (fun ov' -> ov' = ov.mq_outvar) unassigneds
                        then []
                        else [ov.mq_outvar] )
                end
                (Result.Ok ([], unassigneds))
              |> Result.map begin function (upds, unassigneds) ->
                (NonEmptyList.coerce upds, unassigneds)
              end
            in
            let ann =
              Definitions.DataUpdUnassigned
                (List.map
                   (fun ua ->
                      Definitions.({mq_outvar = ua; fieldlike = None}))
                   unassigneds')
            in
            Result.Ok
              ( ModePass.Prog.DataUpd (Some ann, dataupd')
              , Some unassigneds )
        end

      | Subseq {lb = lb; ub = ub} ->
        let* lb' =
          Result.map_option
            (fun x ->
               let* (lb', _) = mode_expr_no_out_vars vars_out ~except:None x in
               Result.Ok lb')
            lb
        in
        let* ub' =
          Result.map_option
            (fun x ->
               let* (ub', _) = mode_expr_no_out_vars vars_out ~except:None x in
               Result.Ok ub')
            ub
        in
        Result.Ok
          ( ModePass.Prog.Subseq {lb = lb'; ub = ub'}
          , no_unassigneds)

      | SliceLen {sublens = sublens; to_end = to_end} ->
        let* sublens' =
          NonEmptyList.as_list sublens
          |> List.mapMResult begin fun sublen ->
            let* (sublen', _) = mode_expr_no_out_vars vars_out ~except:None sublen in
            Result.Ok sublen'
          end
          |> Result.map NonEmptyList.coerce
          (* Result.map NonEmptyList.coerce *)
          (*   (List.mapMResult aux_expr (NonEmptyList.as_list sublens)) *)
        in
        Result.Ok
          ( ModePass.Prog.SliceLen {sublens = sublens'; to_end = to_end}
          , no_unassigneds )

      | SeqUpd {idx = idx; v = v} ->
        let* (idx', _) = mode_expr_no_out_vars vars_out ~except:None idx in
        let* (v', _)   = mode_expr_no_out_vars vars_out ~except:None v in
        Result.Ok
          ( ModePass.Prog.SeqUpd {idx = idx'; v = v'}
          , no_unassigneds )
      | Sel e ->
        let* (e', _) = mode_expr_no_out_vars vars_out ~except:None e in
        Result.Ok (ModePass.Prog.Sel e', no_unassigneds)
      | ArgList (args, ann) ->
        (* NOTE: If no output variables are allowed, no predicates marked for
           functionalization are allowed either *)
        let exists_output = List.exists ((=) Syntax.Annotation.Output) in
        let* () =
          Option.fold ~none:(Result.Ok ())
            ~some:(function (p_id, arg_modes) ->
                Result.error_when (exists_output arg_modes)
                  (lazy
                    { callstack = [here]
                    ; sort = FunctionalizedPredOccur p_id }))
            ann
        in
        let* args_pos' =
          List.mapMResult
            (fun x ->
               let* (x', _) = mode_expr_no_out_vars vars_out ~except:None x in
               Result.Ok x')
            args.positional in
        let* args_nam' =
          List.mapMResult
            begin function (id, arg) ->
              let* (arg', _) = mode_expr_no_out_vars vars_out ~except:None arg in
              Result.Ok (id, arg')
            end
            args.named in
        (* NOTE: We delete the annotation here if all arguments are marked input.
           TODO: This /needs/ changing if we support other user annotations (e.g.,
           name for functionalized code) *)
        Result.Ok
          ( ModePass.Prog.ArgList
              ({ positional = args_pos'
               ; named = args_nam' }
              , None)
          , no_unassigneds )

  and aux_extended_pattern epat =
    Result.map_error
      begin fun err ->
        { callstack = here :: err.callstack
        ; sort = OutVarOccur err.sort }
      end
      (mode_expr_no_out_vars_extended_pattern vars_out epat)

  and aux_pattern pat =
    mode_expr_no_out_vars_pattern vars_out pat
    |> Result.map_error begin fun err ->
      { callstack = here :: err.callstack
      ; sort = OutVarOccur err.sort }
    end
  in

  match e with
  | Suffixed (pref, suff) ->
    let* (pref', unassigned) = mode_expr_no_out_vars vars_out ~except:except pref in
    let* (suff', unassigned) =
      aux_suffix
        ~except:(Option.liftA2 (fun x y -> (x, y)) except unassigned)
        suff
    in
    Result.Ok (ModePass.Prog.Suffixed (pref', suff'), unassigned)
  | NameSeg (seg_id, seg_tp_args) ->
    let* () =
      Result.error_when (Util.id_in_formals seg_id vars_out)
        (lazy
          { callstack = [here]
          ; sort = OutVarOccur {occurring_outvar = seg_id; shadowed = false} })
    in
    let seg_tp_args' = List.map Convert.typ seg_tp_args in
    Result.Ok
      (ModePass.Prog.NameSeg (seg_id, seg_tp_args'), no_unassigneds)

  | Lambda (lam_ps, lam_body) ->
    let* lam_ps' =
      List.mapMResult
        begin function (p_id, p_tp_opt) ->
          let* () =
            Result.error_when (Util.id_in_formals p_id vars_out)
              (lazy
                { callstack = [here]
                ; sort =
                    OutVarOccur
                      { occurring_outvar = p_id
                      ; shadowed = true }})
          in
          Result.Ok (p_id, Option.map Convert.typ p_tp_opt)
        end
        lam_ps
    in
    let* (lam_body', _) = mode_expr_no_out_vars vars_out ~except:None lam_body in
    Result.Ok (ModePass.Prog.Lambda (lam_ps', lam_body'), no_unassigneds)

  | MapDisplay kvs ->
    let* kvs' =
      List.mapMResult
        begin function (k, v) ->
          let* (k', _) = mode_expr_no_out_vars vars_out ~except:None k in
          let* (v', _) = mode_expr_no_out_vars vars_out ~except:None v in
          Result.Ok (k', v')
        end
        kvs
    in
    Result.Ok (ModePass.Prog.MapDisplay kvs', no_unassigneds)

  | SeqDisplay seqd ->
    let* seqd' = begin
      match seqd with
      | SeqEnumerate seqd_enum ->
        let* seqd_enum' =
          seqd_enum
          |> List.mapMResult begin fun e ->
            let* (e', _) = mode_expr_no_out_vars vars_out ~except:None e in
            Result.Ok e'
          end
        in
        Result.Ok (ModePass.Prog.SeqEnumerate seqd_enum')
      | SeqTabulate seqd_tab ->
        let tp_args' = List.map Convert.typ seqd_tab.gen_inst in
        let* (len', _) = mode_expr_no_out_vars vars_out ~except:None seqd_tab.len in
        let* (func', _) = mode_expr_no_out_vars vars_out ~except:None seqd_tab.func in
        Result.Ok
          (ModePass.Prog.SeqTabulate
             { gen_inst = tp_args'
             ; len = len'
             ; func = func' })
    end in
    Result.Ok (ModePass.Prog.SeqDisplay seqd', no_unassigneds)

  | SetDisplay setd ->
    let* setd' =
      setd
      |> List.mapMResult begin fun e ->
        let* (e', _) = mode_expr_no_out_vars vars_out ~except:None e in
        Result.Ok e'
      end
    in
    Result.Ok (ModePass.Prog.SetDisplay setd', no_unassigneds)

  (* TODO: we should be tracking unassigneds like assignments, for now the
     unassigneds analysis is shallow *)
  | If (_, g, t, e) ->
    let* (g', _) = mode_expr_no_out_vars vars_out ~except:None g in
    (* NOTE: These two below need changing for more sophisticated analysis *)
    let* (t', _) = mode_expr_no_out_vars vars_out ~except:None t in
    let* (e', _) = mode_expr_no_out_vars vars_out ~except:None e in
    Result.Ok (ModePass.Prog.If (None, g', t', e'), no_unassigneds)

  (* TODO: we should be tracking unassigneds like assignments, for now the
     unassigneds analysis is shallow *)
  | Match (_, scrut, branches) ->
    let* (scrut', _) = mode_expr_no_out_vars vars_out ~except:None scrut in
    let* branches' =
      List.mapMResult begin function
        | AnnotationPass.Prog.Case (_attrs, e_pat, body) ->
          let attrs' = [] in
          let* e_pat' = aux_extended_pattern e_pat in
          (* NOTE: The line below needs changing for more sophisticated analysis *)
          let* (body', _) = mode_expr_no_out_vars vars_out ~except:None body in
          Result.Ok (ModePass.Prog.Case (attrs', e_pat', body'))
      end branches
    in
    Result.Ok (ModePass.Prog.Match (None, scrut', branches'), no_unassigneds)

  | Quantifier (_, qt) ->
    let* qdom' =
      mode_expr_no_out_vars_quantifier_domain vars_out qt.qdom in
    let* (qbody', _) = mode_expr_no_out_vars vars_out ~except:None qt.qbody in
    Result.Ok ModePass.Prog.(
        ( Quantifier (None, {qt = qt.qt; qdom = qdom'; qbody = qbody'})
        , no_unassigneds ))

  | SetComp setc ->
    let* setc_qdom' =
      mode_expr_no_out_vars_quantifier_domain vars_out setc.qdom in
    let* setc_body' =
      setc.body
      |> Result.map_option begin fun bod ->
        let* (bod', _) = mode_expr_no_out_vars vars_out ~except:None bod in
        Result.Ok bod'
      end
    in
    Result.Ok
      ( ModePass.Prog.SetComp {qdom = setc_qdom'; body = setc_body'}
      , no_unassigneds )

  | StmtInExpr (_, e) ->
    (* NOTE: For now, we (silently) drop statements in expressions
       TODO: Generate something for the user indicating that the
       assert/assume/reveal/etc was dropped *)
    mode_expr_no_out_vars vars_out ~except:except e

  | Let {ghost = ghost; pats = pats; defs = defs; body = body} ->
    let* pats' =
      Result.map NonEmptyList.coerce
        (List.mapMResult aux_pattern
           (NonEmptyList.as_list pats))
    in
    let* defs' =
      (* Result.map NonEmptyList.coerce *)
      (*   (List.mapMResult aux_expr (NonEmptyList.as_list defs)) in *)
      NonEmptyList.as_list defs
      |> List.mapMResult
        begin fun def ->
          let* (def', _) = mode_expr_no_out_vars vars_out ~except:None def in
          Result.Ok def'
        end
      |> Result.map NonEmptyList.coerce
    in
    let* (body', unassigneds) = mode_expr_no_out_vars vars_out ~except:except body in
    Result.Ok (ModePass.Prog.(
        ( Let {ghost = ghost; pats = pats'; defs = defs'; body = body'}
        , unassigneds )))

  | MapComp mapc ->
    let* mapc_qdom' =
      mode_expr_no_out_vars_quantifier_domain vars_out mapc.qdom in
    let* mapc_key' =
      mapc.key
      |> Result.map_option begin fun k ->
        let* (k', _) = mode_expr_no_out_vars vars_out ~except:None k in
        Result.Ok k'
      end
    in
    let* (mapc_valu', _) = mode_expr_no_out_vars vars_out ~except:None mapc.valu in
    Result.Ok
      ( ModePass.Prog.MapComp
          { imap = mapc.imap
          ; qdom = mapc_qdom'
          ; key = mapc_key'
          ; valu = mapc_valu' }
      , no_unassigneds )

  | Lit l ->
    Result.Ok (ModePass.Prog.Lit l, no_unassigneds)

  | This ->
    failwith (here ^ " `this` not supported (should have been caught earlier!)")

  | Cardinality e ->
    let* (e', _) = mode_expr_no_out_vars vars_out ~except:None e in
    Result.Ok (ModePass.Prog.Cardinality e', no_unassigneds)

  (* TODO: tuples have "named" (numbered) components, these could be unassigned *)
  | Tuple es ->
    let* es' =
      es
      |> List.mapMResult begin fun e ->
        let* (e', _) = mode_expr_no_out_vars vars_out ~except:None e in
        Result.Ok e'
      end
    in
    Result.Ok (ModePass.Prog.Tuple es', no_unassigneds)

  | Unary (uop, e) ->
    let* (e', _) = mode_expr_no_out_vars vars_out ~except:None e in
    Result.Ok (ModePass.Prog.Unary (uop, e'), no_unassigneds)

  (* TODO: consider all the binary operations *)
  | Binary (_, bop, e1, e2) ->
    let* (e1', _) = mode_expr_no_out_vars vars_out ~except:None e1 in
    let* (e2', _) = mode_expr_no_out_vars vars_out ~except:None e2 in
    Result.Ok (ModePass.Prog.Binary (None, bop, e1', e2'), no_unassigneds)

  | Lemma {lem = lem; e = e} ->
    let* (lem', _) = mode_expr_no_out_vars vars_out ~except:None lem in
    let* (e', unassigneds) = mode_expr_no_out_vars vars_out ~except:except e in
    Result.Ok (ModePass.Prog.Lemma {lem = lem'; e = e'}, unassigneds)


and mode_expr_no_out_vars_quantifier_domain
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (qdom: AnnotationPass.Prog.qdom_t)
  : ( ModePass.Prog.qdom_t, error_mode_expr_no_out_vars_t) m =
  let here = "Moder.mode_expr_no_out_vars_quantifier_domain:" in

  let QDom {qvars = qvars; qrange = qrange} = qdom in
  let* qvars' =
    List.mapMResult
      begin function
        | AnnotationPass.Prog.QVar (id, tp, dom_col, _attrs) ->
          let* () =
            Result.error_when (Util.id_in_formals id vars_out)
              (lazy
                { callstack = [here]
                ; sort =
                    OutVarOccur
                      { occurring_outvar = id
                      ; shadowed = true }})
          in
          let tp' = Option.map Convert.typ tp in
          let* dom_col' =
            dom_col
            |> Result.map_option begin fun e ->
              let* (e', _) = mode_expr_no_out_vars vars_out e in
              Result.Ok e'
            end
          in
          let attrs' = [] in
          Result.Ok (ModePass.Prog.QVar (id, tp', dom_col', attrs'))
      end
      qvars
  in
  let* qrange' =
    qrange
    |> Result.map_option begin fun e ->
      let* (e', _) = mode_expr_no_out_vars vars_out e in
      Result.Ok e'
    end
  in
  Result.Ok (ModePass.Prog.QDom {qvars = qvars'; qrange = qrange'})

type error_mode_expr_illegal_quantifier_domain_sources_t =
  { collection: bool
  ; range: bool
  ; antecedent: bool }
[@@deriving show, eq]

type error_mode_expr_unsupported_quantifier_domain_sources_t =
  | QDomCollection
  | QDomRange
[@@deriving show, eq]

type error_mode_expr_t =
  | UnsupportedTypeArgs of Definitions.outvar_lhs_t
  | UnsupportedNamedArgs of id_t * AnnotationPass.Prog.expr_t
  | UnsupportedEquatedOutVars of (Definitions.outvar_lhs_t * Definitions.outvar_lhs_t)
  | UnsupportedMultipleUniversalQuantifications of ParserPass.Prog.expr_t
  | FunctionalizedPredOccur of Syntax.Common.module_qualified_name_t
  | MixedIO of
      { input_violation: error_outvar_occur_t
      ; expr: ParserPass.Prog.expr_t }
  | AnnotationViolation of
      { p_id: Syntax.Common.module_qualified_name_t
      ; arg: ParserPass.Prog.expr_t
      ; i_or_o_expected:
          (error_outvar_occur_t, ParserPass.Prog.expr_t) Either.t }
  | InputModeViolation of error_outvar_occur_t * ParserPass.Prog.expr_t
  | OutVarShadowing of id_t
  (* argument is a branch with no output variables assigned *)
  | MixedBranchIO of ParserPass.Prog.expr_t
  | IllegalQuantifierDomainForFunctionalization of
      { domain: ParserPass.Prog.expr_t
      ; src: error_mode_expr_illegal_quantifier_domain_sources_t
      ; quantification: ParserPass.Prog.expr_t }
  | UnsupportedQuantifierDomainSourceForFunctionalization of
      { domain: ParserPass.Prog.expr_t
      ; src: error_mode_expr_unsupported_quantifier_domain_sources_t
      ; quantification: ParserPass.Prog.expr_t }
  | IllegalQuantifierEquivalenceForFunctionalization of
      ParserPass.Prog.expr_t
  | UnsupportedUniversalQuantification of ParserPass.Prog.expr_t
[@@deriving show]

let mode_expr_ensure_input_generalized
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (e: AnnotationPass.Prog.expr_t)
    ~(except: Common.member_qualified_name_t option)
  : ( ModePass.Prog.expr_t * Definitions.outvar_lhs_t list option
    , error_mode_expr_t) m =
  Result.map2' ~res:(mode_expr_no_out_vars vars_out ~except:except e)
    ~ok:begin function (e', unassigneds) ->
      ( e'
      , unassigneds
        |> Option.map
          (List.map (fun ua -> Definitions.({mq_outvar = ua; fieldlike = None}))) )
    end
    ~error:begin fun err ->
      { callstack = err.callstack
      ; sort =
          match (err.sort : error_mode_expr_no_out_vars_t) with
          | OutVarOccur ov_occ ->
            InputModeViolation (ov_occ, Erase.Annotations.expr e)
          | FunctionalizedPredOccur fp_id ->
            FunctionalizedPredOccur fp_id
      }
    end

let mode_expr_ensure_input
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (e: AnnotationPass.Prog.expr_t)
  : ( ModePass.Prog.expr_t, error_mode_expr_t) m =
  let* (e', _) = mode_expr_ensure_input_generalized vars_out e ~except:None in
  Result.Ok e'

let mode_expr_ensure_input_except
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (e: AnnotationPass.Prog.expr_t)
    ~(except: Common.member_qualified_name_t)
  : ( ModePass.Prog.expr_t * Definitions.outvar_lhs_t list
    , error_mode_expr_t) m =
  let* (e', unassigneds) =
    mode_expr_ensure_input_generalized vars_out e ~except:(Some except) in
  Result.Ok (e', Option.get unassigneds)

let mode_expr_ensure_output
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (e: AnnotationPass.Prog.expr_t)
    (on_illegal_outvar_lhs: ParserPass.Prog.expr_t -> error_mode_expr_t)
  : (Definitions.outvar_lhs_t, error_mode_expr_t) m =
  let here = "Moder.mode_expr_ensure_output:" in

  mode_expr_outvar_lhs vars_out e
  |> Result.map_error begin fun err ->
    { callstack = here :: err.callstack
    ; sort =
        match (err.sort : error_mode_expr_outvar_lhs_t) with
        | UnsupportedTypeArgs ov ->
          UnsupportedTypeArgs ov
        | IllegalOutVarLHS offending ->
          on_illegal_outvar_lhs offending }
    end

type mode_expr_analyze_t =
  | OutputModed of Definitions.outvar_lhs_t
  | InputModed of ModePass.Prog.expr_t
  | MixedModed of error_outvar_occur_t

let mode_expr_analyze
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (e: AnnotationPass.Prog.expr_t)
  : (mode_expr_analyze_t, error_mode_expr_t) m =
  match mode_expr_outvar_lhs vars_out e with
  | Result.Ok lhs -> Result.Ok (OutputModed lhs)
  | Result.Error err -> begin
      match err.sort with
      | UnsupportedTypeArgs lhs ->
        Result.Error
          { callstack = err.callstack
          ; sort = UnsupportedTypeArgs lhs }
      | IllegalOutVarLHS _offending ->
        mode_expr_no_out_vars vars_out e
        |> Result.fold
             ~ok:(fun x -> Result.Ok (InputModed (fst x)))
             ~error:begin fun err2 ->
               match err2.sort with
               | OutVarOccur ov_occ ->
                 Result.Ok (MixedModed ov_occ)
               | FunctionalizedPredOccur fp_occ ->
                 Result.Error
                   { callstack = err2.callstack
                   ; sort = FunctionalizedPredOccur fp_occ
                   }
             end
    end

let rec mode_expr
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (expr: AnnotationPass.Prog.expr_t)
  : ( ModePass.Prog.expr_t * Definitions.outvar_lhs_t list
    , error_mode_expr_t ) m =
  let _here = "Moder.mode_expr" in

  match expr with
  | Let {ghost = g; pats = pats; defs = defs; body = body} ->
    let* pats' =
      NonEmptyList.as_list pats
      |> List.mapMResult (mode_expr_no_out_vars_pattern vars_out)
      |> Result.map NonEmptyList.coerce
      |> Result.map_error (fun err ->
          { callstack = err.callstack
          ; sort = OutVarShadowing err.sort.occurring_outvar })
    in
    let* defs' =
      NonEmptyList.as_list defs
      |> List.mapMResult (mode_expr_ensure_input vars_out)
      |> Result.map NonEmptyList.coerce
    in
    let* (body', ovs) = mode_expr vars_out body in
    Result.Ok
      ( ModePass.Prog.(
            Let { ghost = g
                ; pats = pats'
                ; defs = defs'
                ; body = body' })
      , ovs )
  | _ ->
    let conjs = AnnotationPass.Prog.to_conjuncts expr in
    let* conjs' =
      List.mapMResult (mode_expr_conjunct vars_out) conjs
    in

    Result.Ok
      (ModePass.Prog.assoc_right_bop_ann
         Common.And conjs'
         (fun ovs1 ovs2 ->
            ( Some (Definitions.And {conj_left = ovs1; conj_right = ovs2})
            , ovs1 @ ovs2 ))
         ( ModePass.Prog.Lit Common.True
         , [] ))


and mode_expr_conjunct_eq
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (e1: AnnotationPass.Prog.expr_t) (e2: AnnotationPass.Prog.expr_t)
  : ( ModePass.Prog.expr_t * Definitions.outvar_lhs_t list
    , error_mode_expr_t ) m =
  let here = "Moder.mode_expr_conjunct_eq" in

  let order_equated ov e is_left =
    if is_left then
      (Util.outvar_lhs_to_modepass_expr ov, e)
    else
      (e, Util.outvar_lhs_to_modepass_expr ov)
  in

  let build_simple ov e is_left =
    let ann =
      Some Definitions.(
          { outvar_is_left = is_left
          ; outvar = ov
          ; unassigned_members = Some [] })
    in
    let (e1, e2) = order_equated ov e is_left in
    Result.Ok (e1, e2, ann)
  in

  let build_with_unassigned ov e is_left =
    let* (e', unassigned) =
      mode_expr_no_out_vars vars_out
        ~except:(Some Definitions.(ov.mq_outvar)) e
      |> Result.catch begin fun err ->
        Result.Error
          { callstack = err.callstack
          ; sort =
              match err.sort with
              | OutVarOccur ov_occ ->
                InputModeViolation (ov_occ, Erase.Annotations.expr e)
              | FunctionalizedPredOccur fp_occ ->
                FunctionalizedPredOccur fp_occ
          }
      end in

    let ann =
      Some Definitions.(
          { outvar_is_left = is_left
          ; outvar = ov
          ; unassigned_members = unassigned })
    in
    let (e1, e2) = order_equated ov e' is_left in
    Result.Ok (e1, e2, ann)
  in

  let* (e1', e2', ann) =
    on_error_push_callstack here begin
      let* e1_analysis = mode_expr_analyze vars_out e1 in
      let* e2_analysis = mode_expr_analyze vars_out e2 in

      (* Determine the annotation, or error if both are outvar_lhss *)
      match (e1_analysis, e2_analysis) with
      | (OutputModed ov1, OutputModed ov2) ->
        Result.Error
          { callstack = []
          ; sort = UnsupportedEquatedOutVars (ov1, ov2) }
      | (InputModed e1, InputModed e2) ->
        Result.Ok (e1, e2, None)
      | (OutputModed ov, InputModed e) ->
        build_simple ov e true
      | (InputModed e, OutputModed ov) ->
        build_simple ov e false
      | (OutputModed ov, MixedModed _) ->
        build_with_unassigned ov e2 true
      | (MixedModed _ov_occ, OutputModed ov) ->
        build_with_unassigned ov e1 false
      | (MixedModed ov_occ, _) ->
        Result.Error
          { callstack = []
          ; sort = InputModeViolation (ov_occ, Erase.Annotations.expr e1) }
      | (_, MixedModed ov_occ) ->
        Result.Error
          { callstack = []
          ; sort = InputModeViolation (ov_occ, Erase.Annotations.expr e2) }
    end
  in

  Result.Ok
    ( ModePass.Prog.Binary
        ( Option.map (fun x -> Definitions.Eq x) ann
        , Syntax.Common.Eq, e1', e2')
    , Option.fold ~none:[]
        ~some:(fun ann_eq -> [Definitions.(ann_eq.outvar)])
        ann)

and mode_expr_conjunct_arglist_functionalize
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (pref: Syntax.Common.module_qualified_name_t)
    (args: AnnotationPass.Prog.arglist_t)
    (modes: Annotation.mode_t list)
  : ( ModePass.Prog.expr_t * Definitions.outvar_lhs_t list
    , error_mode_expr_t ) m =
  let here = "Moder.mode_expr_conjunct_arglist_functionalize:" in

  let ( PositionalPartition {args_in = args_in; args_out = args_out}
      , named_args_p ) =
    Util.partition_args_by_modes args modes in

  (* TODO: We don't support named arguments in our mode analysis (yet) *)
  let* () =
    Result.error_when named_args_p
      (lazy
        { callstack = [here]
        ; sort =
            let (id, arg) = List.nth args.named 0 in
            UnsupportedNamedArgs (id, arg) })
  in
  (* Check arguments in input positions contain not output-moded variables, and
     arguments in output positions are valid outvar lhs *)
  let* args_in' =
    args_in
    |> List.mapMResult begin fun arg_in ->
      mode_expr_ensure_input vars_out arg_in
      |> Result.map_error begin fun err ->
        { callstack = err.callstack
        ; sort =
            match err.sort with
            | InputModeViolation (ov_occ, arg_in_erased) ->
              AnnotationViolation
                { p_id = pref
                ; arg = arg_in_erased
                ; i_or_o_expected = Either.Left ov_occ }
            | _ as es -> es }
        end
    end
  in

  let* args_out' =
    args_out
    |> List.mapMResult begin fun arg_out ->
        mode_expr_ensure_output vars_out arg_out begin fun illegalLHS ->
          AnnotationViolation
            { p_id = pref
            ; arg = Erase.Annotations.expr arg_out
            ; i_or_o_expected = Either.Right illegalLHS }
        end
      end
  in

  Result.Ok
    ( ModePass.Prog.(
          Suffixed
            ( from_qualified_id pref
            , ArgList
                ({ positional =
                     Util.assemble_positional_args_by_modes
                       args_in' args_out' modes
                 ; named = []     (* TODO: named args *) }
                , Some
                   { callee = pref
                   ; in_exprs = List.map Erase.Modings.expr args_in'
                   ; out_vars = args_out' })))
    , args_out' )

and mode_expr_conjunct_if
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (guard: AnnotationPass.Prog.expr_t)
    (then_: AnnotationPass.Prog.expr_t)
    (else_: AnnotationPass.Prog.expr_t)
  : ( ModePass.Prog.expr_t * Definitions.outvar_lhs_t list
    , error_mode_expr_t ) m =
  let here = "Moder.mode_expr_conjunct_if:" in

  on_error_push_callstack here begin
    (* Check that the guard is correctly input moded *)
    let* guard' = mode_expr_ensure_input vars_out guard in
    let* (then_', then_ovs) = mode_expr vars_out then_ in
    let* (else_', else_ovs) = mode_expr vars_out else_ in
    let* ann = begin
      match (then_ovs, else_ovs) with
      | (_ :: _, _ :: _) ->
        let ann =
          Definitions.(
            { vars_then = NonEmptyList.coerce then_ovs
            ; vars_else = NonEmptyList.coerce else_ovs }) in
        Result.Ok (Some ann)
      | ([], []) -> Result.Ok None
      | _ ->
        let outvarless =
          if List.length then_ovs = 0 then then_' else else_' in
        Result.Error
          { callstack = []
          ; sort = MixedBranchIO (Erase.Modings.expr outvarless) }
    end in

    Result.Ok
      ( ModePass.Prog.If (ann, guard', then_', else_')
      , Option.fold ~none:[]
          ~some:begin fun an ->
            let ovs = Definitions.(an.vars_then) in
            NonEmptyList.as_list ovs
          end
          ann )
  end

and mode_expr_conjunct_match
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (scrut: AnnotationPass.Prog.expr_t)
    (tree: AnnotationPass.Prog.case_expr_t list)
  : ( ModePass.Prog.expr_t * Definitions.outvar_lhs_t list
    , error_mode_expr_t ) m =
  let orig = AnnotationPass.Prog.Match ((), scrut, tree) in
  let here = "Moder.mode_expr_conjunct_match:" in

  let* scrut' = mode_expr_ensure_input vars_out scrut in
  let* tree' =
    tree |>
    List.mapMResult
      begin function AnnotationPass.Prog.Case (_attrs, epat, body) ->
        let* epat' =
          Result.map_error
            begin fun err ->
              { callstack = here :: err.callstack
              ; sort =
                  InputModeViolation (err.sort, Erase.Annotations.expr orig) }
            end
            (mode_expr_no_out_vars_extended_pattern vars_out epat)
        in
        let* (body', ovs) = mode_expr vars_out body in
        Result.Ok
          ( ModePass.Prog.Case([], epat', body')
          , NonEmptyList.from_list_opt ovs)
      end
  in

  let (o_moded, i_moded) =
    tree' |>
    List.partition_map
      (function (ModePass.Prog.Case (_, _, body), ovs) ->
         Option.fold ~none:(Either.Right body) ~some:Either.left ovs)
  in

  let* ann: ModingMetaData.match_t =
    match (o_moded, i_moded) with
    | (_, []) -> Result.Ok (Some (NonEmptyList.coerce o_moded))
    | ([], _) -> Result.Ok None
    | (_, offending :: _) ->
      Result.Error
        { callstack = [here]
        ; sort = MixedBranchIO (Erase.Modings.expr offending) }
  in

  Result.Ok
    ( ModePass.Prog.Match (ann, scrut', List.map fst tree')
    , ann |>
      Option.fold ~none:[]
        ~some:(fun a -> NonEmptyList.(as_list (head a))) )

(* BEGIN WIP *)
and mode_expr_conjunct_forall
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (qdom: AnnotationPass.Prog.qdom_t)
    (qbody: AnnotationPass.Prog.expr_t)
  : ( ModePass.Prog.expr_t * Definitions.outvar_lhs_t list
    , error_mode_expr_t ) m =
  let here = "Moder: mode_expr_conjunct_forall:" in
  let orig =
    AnnotationPass.Prog.Quantifier
      ( ()
      , { qt = Syntax.Common.Forall
        ; qdom = qdom
        ; qbody = qbody })
  in
  let erase_orig() = Erase.Annotations.expr orig in

  let QDom {qvars = qvars; qrange = qrange} = qdom in

  (* BEGIN utilities *)
  (* NOTE: We only support a single output variable *)
  let ensure_single_fresh_qvar
      (qvars: AnnotationPass.Prog.qvar_decl_t list) =
    match qvars with
    | (QVar (qv_id, _, _, _) as qvar) :: []
      when not (Util.id_in_formals qv_id vars_out) ->
      Result.Ok qvar
    | (QVar (qv_id, _, _, _)) :: [] ->
      Result.Error
        { callstack = [here]
        ; sort = OutVarShadowing qv_id }
    | _ ->
      Result.Error
        { callstack = [here]
        ; sort =
            UnsupportedMultipleUniversalQuantifications (erase_orig()) }

  in
  let determine_outvar_for_qvar
      (qv_id: Syntax.id_t)
      (qv_tp: AnnotationPass.Type.t option)
      (qv_dom_coll: AnnotationPass.Prog.expr_t option)
      (qrange: AnnotationPass.Prog.expr_t option)
      (qbody: AnnotationPass.Prog.expr_t)
    : ( ModePass.Prog.expr_t * Definitions.outvar_lhs_t list
      , error_mode_expr_t ) m =
    (* TODO: When we support collection domains and domain restrictions
       ("ranges"), switch to error IllegalQuantifierDomainForFunctionalization
       if we ever have more than one (or no) sources *)
    let err_unsupported_qdom dom src =
      UnsupportedQuantifierDomainSourceForFunctionalization
        { domain = Erase.Annotations.expr dom
        ; src = src
        ; quantification = erase_orig() }
    in
    let err_illegal_qdom dom src =
      IllegalQuantifierDomainForFunctionalization
        { domain = Erase.Annotations.expr dom
        ; src = src
        ; quantification = erase_orig() }
    in

    let try_numeric_range_antecedent = function
      (* TODO: Would be nice to have a less hacky analysis *)
      | AnnotationPass.Prog.Binary (_, And, r1, r2) -> begin
          match (r1, r2) with
          (* 0 <= qv_id < |outvar| *)
          | ( Binary (_, Lte, Lit (Nat 0), NameSeg (q1, []))
            , Binary (_, Lt, NameSeg (q2, []), (Cardinality _ as ub)))
            when q1 = q2 && q2 = qv_id ->
            mode_expr_outvar_lhs vars_out ub
            |> Result.fold ~error:(Fun.const Option.None)
              ~ok:begin fun ov ->
                assert Definitions.(ov.fieldlike = Some Cardinality);
                Option.Some Definitions.(
                    { id = qv_id; tp = qv_tp
                    ; domain = (QFVarRangeBounds, ov) })
              end
          | _ ->
            Option.None
      end
      | _ ->
        Option.None
    in
    let try_collection_membership_antecedent = function
      | AnnotationPass.Prog.Binary
          (_, In, NameSeg (q1, []), coll) when q1 = qv_id -> begin
          mode_expr_outvar_lhs vars_out coll
          |> Result.fold ~error:(Fun.const Option.None)
            ~ok:begin fun ov ->
              if Option.is_some Definitions.(ov.fieldlike) then
                Option.None
              else
                Option.Some Definitions.(
                    { id = qv_id; tp = qv_tp
                    ; domain = (QFVarRangeColl, ov) })
            end
        end
      | _ -> Option.None
    in
    let try_antecedent e =
      begin                     (* to avoid both attempts being evaluated (OCaml is call-by-value) *)
        try_numeric_range_antecedent e
        |> Option.fold
          ~some:(fun x -> Fun.const (Some x))
          ~none:(fun () -> try_collection_membership_antecedent e)
      end ()
    in

    match (qv_dom_coll, qrange, qbody) with
    | (Some coll, _, _) ->
      Result.Error
        { callstack = [here]
        ; sort = err_unsupported_qdom coll QDomCollection }
    | (None, Some range, _) ->
      Result.Error
        { callstack = [here]
        ; sort = err_unsupported_qdom range QDomRange }
    | (None, None, Binary (_, Syntax.Common.Implies, ante, consq)) -> begin
        match try_antecedent ante with
        | None ->
          Result.Error
            { callstack = [here]
            ; sort =
                err_illegal_qdom ante
                  { collection = false
                  ; range = false
                  ; antecedent = true }}
        | Some qrange' ->
          (* TODO Hacky *)
          let* (consq', ovs) = mode_expr vars_out consq in
          let ann = Definitions.({qvar = QFVarRange qrange'; body_outvars = ovs}) in
          let ante' = Convert.expr ante in
          let qdom' = begin
            match (fst qrange'.domain) with
            | QFVarRangeBounds ->
              let qvar' =
                ModePass.Prog.QVar
                  (qv_id, Option.map Convert.typ qv_tp, None, []) in
              ModePass.Prog.QDom {qvars = [qvar']; qrange = Some ante'}
            | QFVarRangeColl ->
              let qvar' =
                ModePass.Prog.QVar
                  ( qv_id, Option.map Convert.typ qv_tp
                  , Some Util.(outvar_lhs_to_modepass_expr (snd qrange'.domain)), [])
              in
              ModePass.Prog.QDom {qvars = [qvar']; qrange = None}
          end in
          Result.Ok
            ( ModePass.Prog.(
                  Quantifier
                    ( Some ann
                    , {qt = Forall; qdom = qdom'; qbody = consq'} ))
            , (snd qrange'.domain) :: ovs )
      end
    (* TODO: equivalences are symmetric... *)
    | ( None, None
      , (Binary
           (_, Equiv, Binary (_, In, NameSeg (q', []), coll), e2)
         as body))
      when q' = qv_id ->
      begin
        let* _ = mode_expr_ensure_input vars_out e2 in
        let* ov =
          mode_expr_ensure_output vars_out coll
            (fun _ ->  (* dummy *)
               IllegalQuantifierEquivalenceForFunctionalization
                (Lit True))
        in
        let qvar' =
          ModePass.Prog.QVar
            (qv_id, Option.map Convert.typ qv_tp, None, [])
        in
        let qdom' =
          ModePass.Prog.(
            QDom {qvars = [qvar']; qrange = None})
        in
        Result.Ok ModePass.Prog.(
            ( Quantifier
                ( Some Definitions.({qvar = QFVarDom ov; body_outvars = []})
                , {qt = Forall; qdom = qdom'; qbody = Convert.expr body })
            , [ov] ))
      end |> Result.map_error begin fun _ ->
        { callstack = [here]    (* override *)
        ; sort =
            IllegalQuantifierEquivalenceForFunctionalization
              (Erase.Annotations.expr qbody) }
      end
    | (None, None, e) ->
      Result.Error
        { callstack = [here]
        ; sort =
            UnsupportedUniversalQuantification
              (Erase.Annotations.expr e) }

  in
  (* END utilities *)

  Result.try_catch begin
    mode_expr_ensure_input vars_out orig
    |> Result.map (fun e -> (e, []))
  end begin fun _ ->
    (* There's an outvar *somewhere* *)

    let* QVar (qv_id, qv_tp, qv_dom_coll, _attrs) =
      ensure_single_fresh_qvar qvars in

    determine_outvar_for_qvar qv_id qv_tp qv_dom_coll qrange qbody
  end
(* END WIP *)

  (* Questions to answer:
   *
   * 1. is the domain of the quantifier generated from something?

   *    a. if so, it should be something we recognize (natural number bound or a
           collection) involving an outvar
  *)

  (* NOTE: The type /could/ tell us what collection is being drawn from, but
     we're unable to perform that kind of analysis *)
  (* match (qv_dom_coll, qrange, qbody) with *)
  (* | Some qv_dom_coll, None, _ -> begin *)
  (*     let* coll_analysis = mode_expr_analyze vars_out qv_dom_coll in *)
  (*     match coll_analysis with *)
  (*     | Either.Right _ -> *)
  (*       (\* If the collection is present and input-moded, check the entire *)
  (*          quantification is input-moded *\) *)
  (*       mode_expr_ensure_input vars_out orig *)
  (*       |> Result.map (fun e -> (e, [])) *)
  (*     | Either.Left ov -> *)
  (*       let () = *)
  (*         Option.fold ~none:() *)
  (*           ~some:(function Definitions.Cardinality -> *)
  (*               failwith (here ^ " [fatal] type error: cardinality expressions cannot produce collections")) *)
  (*           ov.uop *)
  (*       in *)
  (*       (\* TODO: The following assumes cardinality is the only field-like *)
  (*          operation. This is likely to change *\) *)
  (*       foo12 *)
  (*   end *)
  (* | None, Some qrange, _ -> foo2 *)
  (* | None, None, _ -> foo3 *)
  (* | Some _, Some _, _ -> _ *)

and mode_expr_conjunct
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (conj: AnnotationPass.Prog.expr_t)
  : ( ModePass.Prog.expr_t * Definitions.outvar_lhs_t list
    , error_mode_expr_t ) m =
  let here = "Moder.mode_expr_conjunct:" in

  let aux_name (e: AnnotationPass.Prog.expr_t) =
    let* analysis = mode_expr_analyze vars_out e in
    match analysis with
    | OutputModed ov ->
      let orig' = Util.outvar_lhs_to_modepass_expr ov in
      let inserted_ann =
        Definitions.(Eq {outvar_is_left = true; outvar = ov; unassigned_members = None}) in
      Result.Ok
        ( ModePass.Prog.(
              Binary
                ( Some inserted_ann
                , Common.Eq, orig', Lit True ))
        , [ov] )
    | InputModed e ->
      Result.Ok (e, [])
    | MixedModed ov_occ ->
      Result.Error
        { callstack = [here]
        ; sort =
            MixedIO
              { input_violation = ov_occ
              ; expr = Erase.Annotations.expr e }}
  in

  let aux_suffix pref (suff: AnnotationPass.Prog.suffix_t) =
    let orig = AnnotationPass.Prog.Suffixed (pref, suff) in

    match suff with
    | AugDot (_, _) ->
      aux_name orig
    | DataUpd _ ->
      failwith (here ^ " [fatal] unexpected data update")
    | Subseq _ ->
      failwith (here ^ " [fatal] unexpected subsequence")
    | SliceLen _ ->
      failwith (here ^ " [fatal] unexpected subsequence slices")
    | SeqUpd _ ->
      failwith (here ^ " [fatal] unexpected sequence update")
    | Sel _ ->
      failwith (here ^ " TODO sequence selection not yet supported")

    | ArgList (args, Some (fp_id, modes)) ->
      mode_expr_conjunct_arglist_functionalize vars_out fp_id args modes
    | ArgList (_, None) ->
      (* NOTE: No annotations means we assume everything is input-moded *)
      let* res = mode_expr_ensure_input vars_out orig in
      Result.Ok (res, [])
  in
  let aux_bop e1 e2 bop =
    match bop with
    | Syntax.Common.Eq ->
      mode_expr_conjunct_eq vars_out e1 e2
    (* Type errors *)
    | Mul
    | Div
    | Mod
    | Add
    | Sub ->
      failwith
        (here
         ^ " [fatal] unexpected arithmetic operator: "
         ^ Syntax.Common.(show_bop_t bop))
    (* Not supported for functionalization; ensure input moded *)
    | Neq
    | Lt
    | Gt
    | Lte
    | Gte
    | In
    | Nin
    | Disjoint
    | Or
    | Implies
    | Equiv ->
      let* e1' = mode_expr_ensure_input vars_out e1 in
      let* e2' = mode_expr_ensure_input vars_out e2 in
      Result.Ok
        ( ModePass.Prog.Binary
            (None, bop, e1', e2')
        , [] )
    | And ->
      invalid_arg (here ^ " expected a single conunct, found a conjunction")
  in

  on_error_push_callstack here begin
    match conj with
    | Suffixed (pref, suff) ->
      aux_suffix pref suff
    | NameSeg _ ->
      aux_name conj
    | Lambda (_, _) ->
      failwith (here ^ " [fatal] unexpected lambda")
    | MapDisplay _ ->
      failwith (here ^ " [fatal] unexpected map display")
    | SeqDisplay _ ->
      failwith (here ^ " [fatal] unexpected sequence display")
    | SetDisplay _ ->
      failwith (here ^ " [fatal] unexpected set display")
    | If (_, g, t, e) ->
      mode_expr_conjunct_if vars_out g t e
    | Match (_, scrut, tree) ->
      mode_expr_conjunct_match vars_out scrut tree
    | Quantifier (_, quantification) -> begin
        match quantification.qt with
        | Exists ->
          mode_expr_ensure_input vars_out conj
          |> Result.map (fun x -> (x, []))
        | Forall ->
          (* TODO *)
          mode_expr_conjunct_forall vars_out quantification.qdom quantification.qbody
      end
    | SetComp _ ->
      failwith (here ^ " [fatal] unexpected set comprehension")
    | StmtInExpr (_, body) ->
      (* NOTE: We drop assert/assume statements (and others) *)
      mode_expr vars_out body
    | Let {ghost = ghost; pats = pats; defs = defs; body = body} ->
      let* pats' =
        NonEmptyList.as_list pats
        |> List.mapMResult
          (mode_expr_no_out_vars_pattern vars_out)
        |> Result.map_error begin fun err ->
          { callstack = err.callstack
          ; sort =
              let {occurring_outvar = ov; shadowed = _} = err.sort in
              OutVarShadowing ov }
        end
        |> Result.map NonEmptyList.coerce
      in
      let* defs' =
        NonEmptyList.as_list defs
        |> List.mapMResult (mode_expr_ensure_input vars_out)
        |> Result.map NonEmptyList.coerce
      in
      let* (body', ovs) = mode_expr vars_out body in
      Result.Ok
        ( ModePass.Prog.Let
            { ghost = ghost; pats = pats'
            ; defs = defs'
            ; body = body' }
        , ovs )
    | MapComp _ ->
      failwith (here ^ " [fatal] unexpected map comprehension")
    | Lit l ->
      Result.Ok (ModePass.Prog.Lit l, [])
    | This ->
      failwith (here ^ " [fatal] unexpected `this`")
    | Cardinality _ ->
      failwith (here ^ " [fatal] unexpected cardinality")
    | Tuple _ ->
      failwith (here ^ " [fatal] unexpected tuple")
    | Unary (uop, e) -> begin
        let* (e', ovs) = mode_expr vars_out e in
        Result.Ok
          ( ModePass.Prog.Unary (uop, e')
          , ovs )
      end
    | Binary (_, bop, e1, e2) ->
      aux_bop e1 e2 bop
    | Lemma {lem = _; e = body} ->
      (* NOTE: We drop lemma invocations *)
      mode_expr vars_out body
  end

let mode_topdecl_formals
    (ps: AnnotationPass.TopDecl.formal_t list)
    (ps_ann: AnnotationMetaData.predicate_decl_t)
  : ( ModePass.TopDecl.formal_t list
    * ModingMetaData.predicate_decl_t option ) =
  let ps' =
    List.map
      (function
        | AnnotationPass.TopDecl.Formal (ghost, id, tp) ->
          ModePass.TopDecl.Formal (ghost, id, Convert.typ tp))
      ps
  in
  let ps_ann' =
    Option.map
      (fun pred_modes ->
         let (ps_in, ps_out) =
           List.map2 (fun x y -> (x, y)) ps pred_modes
           |> List.partition_map
                (function
                 | (p, Annotation.Input)  -> Left p
                 | (p, Annotation.Output) -> Right p)
         in
         if List.length ps_out = 0 then
           Definitions.Predicate
         else
           Definitions.Function
             { make_stub = false (* TODO: Ugly dummy value! *)
             ; vars_in = ps_in
             ; vars_out = NonEmptyList.coerce ps_out (* Justified by ite guard *) })
      ps_ann
  in
  (ps', ps_ann')

let mode_topdecl_datatype (dd: AnnotationPass.TopDecl.datatype_t)
  : ModePass.TopDecl.datatype_t =
  let aux_ctor (ctor: AnnotationPass.TopDecl.datatype_ctor_t)
    : ModePass.TopDecl.datatype_ctor_t =
    let DataCtor (_attrs, ctor_id, ps) = ctor in
    let (ps', _) = mode_topdecl_formals ps None in
    (* NOTE: We drop attributes *)
    DataCtor ([], ctor_id, ps')
  in

  let (dd_ann, _attrs, dd_id, _tp_ps, dd_ctors) = dd in
  let dd_ctors' = NonEmptyList.map aux_ctor dd_ctors in
  (* NOTE: We drop attributes, and assume no type arguments *)
  (dd_ann, [], dd_id, [], dd_ctors')

let mode_topdecl_synonym_type
    (sd: AnnotationPass.TopDecl.synonym_type_t)
  : ModePass.TopDecl.synonym_type_t =
  let sd_rhs = begin
    match sd.rhs with
    | Subset (_, _, _) ->
      failwith "Annotator.mode_topdecl_synonym_type: [fatal] unsupported subset types"
    | Synonym t_rhs_tp ->
      ModePass.TopDecl.Synonym (Convert.typ t_rhs_tp)
  end in
  (* NOTE: We drop attributes *)
  ModePass.TopDecl.(
    { ann = sd.ann
    ; attrs = []
    ; id = sd.id
    ; params = sd.params
    ; rhs = sd_rhs })

open struct
  type ('a, 'e) error_logger = 'a * ('e error_t) list
  (* [@@deriving show] *)

  let return (x: 'a): ('a, 'e) error_logger =
    (x, [])

  let ( let< )
      (f: ('a, 'e) error_logger) (g: 'a -> ('b, 'e) error_logger)
    : ('b, 'e) error_logger =
    let (x, logs1) = f in
    let (y, logs2) = g x in
    (y, logs1 @ logs2)

  let log_error (err: 'e error_t): (unit, 'e) error_logger =
    ((), [err])
end

type error_mode_topdecl_t =
  | ErrorModeExpr of error_mode_expr_t
  | ErrorOtherTopDecl of string
[@@deriving show]

let error_mode_expr err = ErrorModeExpr err

let rec mode_topdecl (d: AnnotationPass.TopDecl.t')
  : (ModePass.TopDecl.t' option, error_mode_topdecl_t) error_logger =
  let here = "Moder.mode_topdecl:" in
  let report_offending_predicate p_id err =
    let msg = here ^ " in predicate " ^ p_id in
    { callstack = msg :: err.callstack
    ; sort = ErrorModeExpr err.sort }
  in

  let aux_spec (spec: AnnotationPass.TopDecl.function_spec_t)
    : ModePass.TopDecl.function_spec_t =
    match spec with
    | Reads e -> ModePass.TopDecl.Reads (Convert.expr e)
    | Requires e -> ModePass.TopDecl.Requires (Convert.expr e)
    | Ensures e -> ModePass.TopDecl.Ensures (Convert.expr e)
    | Decreases e -> ModePass.TopDecl.Decreases (Convert.expr e)
  in

  match d with
  | ModuleImport imp ->
    return (Some (ModePass.TopDecl.ModuleImport imp))
  | ModuleDef (_attrs, m_id, m_decls) ->
    let< m_decls' = mode_topdecls m_decls in
    (* NOTE: We drop attributes *)
    return (Some (ModePass.TopDecl.ModuleDef ([], m_id, m_decls')))
  | DatatypeDecl dd ->
    let dd' = mode_topdecl_datatype dd in
    return (Some (ModePass.TopDecl.DatatypeDecl dd'))
  | SynonymTypeDecl syn ->
    let syn' = mode_topdecl_synonym_type syn in
    return (Some (ModePass.TopDecl.SynonymTypeDecl syn'))
  | PredFunDecl
      (Function (m_pres, _attrs, f_id, tp_ps, ps, tp, specs, body)) ->

    let (ps', _) = mode_topdecl_formals ps None in
    let tp' = Convert.typ tp in
    let specs' = List.map aux_spec specs in
    let body' = Convert.expr body in

    return (Some (ModePass.TopDecl.(
        PredFunDecl (Function (m_pres, [], f_id, tp_ps, ps', tp', specs', body')))))

  | PredFunDecl
      (Predicate
         ( p_ann, method_present, _attrs
         , p_id, tp_ps, ps
         , specs, body )) ->

    let (ps', p_ann') = mode_topdecl_formals ps p_ann in
    let specs' = List.map aux_spec specs in

    let generate_result
        (ann: Definitions.predicate_decl_t)
        (p_body: ModePass.Prog.expr_t)
      : ModePass.TopDecl.t' =
      ModePass.TopDecl.PredFunDecl
        (Predicate
           ( ann, method_present, []
           , p_id, tp_ps, ps'
           , specs', p_body ))
    in
    let fallback_result() =
      generate_result Definitions.Predicate (Convert.expr body)
    in

    begin
      match p_ann' with
      | None
      | Some Definitions.Predicate ->
        return (Some (fallback_result ()))
      | Some
          (Definitions.Function
             { make_stub = _      (* TODO: This field has no semantic meaning when
                                     returned from `mode_topdecl_formals` *)
             ; vars_in = vars_in
             ; vars_out = vars_out }) ->

        begin                   (* (ModePass.Prog.expr_t, error_mode_expr_t) m *)
          let* (body', _assigned_outvars) =
            mode_expr (NonEmptyList.as_list vars_out) body in
          Result.Ok
            (generate_result
               Definitions.(
                 Function
                   { make_stub = false
                   ; vars_in = vars_in
                   ; vars_out = vars_out })
               body')
        end |> Result.fold
          ~ok:(fun res -> return (Some res))
          ~error:begin fun err ->
            let< () = log_error (report_offending_predicate p_id err) in
            return (Some (fallback_result ()))
          end
    end
  | MethLemDecl methlem -> begin
      match methlem.sort with
      | Syntax.Common.Method ->
        failwith (here ^ " TODO methods not yet supported")
      | Syntax.Common.Lemma ->
        let< () =
          log_error
            { callstack = [here]
            ; sort =
                ErrorOtherTopDecl (here ^ " [WARN] lemma dropped: " ^ methlem.id) }
        in
        return None
    end

    (* failwith (here ^ " TODO method/lemma unimplemented") *)

and mode_topdecls (d: AnnotationPass.TopDecl.t list)
  : (ModePass.TopDecl.t list, error_mode_topdecl_t) error_logger =
  match d with
  | [] -> return []
  | (mods, decl) :: decls ->
    let< decl' = mode_topdecl decl in
    let< decls' = mode_topdecls decls in

    begin
      match decl' with
      | None -> []
      | Some decl' -> [(mods, decl')]
    end @ decls'
    |> return

let run (m: AnnotationPass.t): (ModePass.t, error_mode_topdecl_t) error_logger =
  let Dafny {includes = includes; decls = decls} = m in
  let< decls' = mode_topdecls decls in
  return (ModePass.Dafny {includes = includes; decls = decls'})
