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

type 'a m = (('a * bool), string) Result.t

(* open struct *)
(*   let return (x: 'a): 'a m = *)
(*     Result.Ok (x, false) *)

(*   let ( let* ) (x: 'a m) (f: 'a -> 'b m): 'b m = *)
(*     let ( let*! ) = Result.bind in *)
(*     let*! (x', b1) = x in *)
(*     let*! (y, b2)  = f x' in *)
(*     Result.Ok (y, b1 || b2) *)

(*   let make_stub (): unit m = *)
(*     Result.Ok ((), true) *)
(* end *)

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
end

(* Check that an expression contains no output-moded (member-qualified) variables
 * Return value is to be interpreted as follows:
 * - None: no output vars in expression
 *
 * - Some mq_var: mq_var is an output-moded formal paremeter that occurs in the
   given expression
*)
(* let rec no_out_vars_expr *)
(*     (vars_out: AnnotationPass.TopDecl.formal_t list) *)
(*     (e: AnnotationPass.Prog.expr_t) *)
(*   : Syntax.Common.member_qualified_name_t option = *)
(*   match e with *)
(*   | Suffixed (e_prefix, suff) -> *)
(*     let mode_prefix = no_out_vars_expr vars_out e_prefix in *)
(*     if Option.is_some mode_prefix then mode_prefix else begin *)
(*       foo_suffixed_suff *)
(*     end *)
(*   | NameSeg seg -> *)
(*     foo_seg *)
(*   | Lambda (ps, body) -> *)
(*     foo_lambda *)
(*   | MapDisplay _ -> *)
(*     foo_mapdisplay *)
(*   | SeqDisplay _ -> *)
(*     foo_seqdisplay *)
(*   | SetDisplay _ -> *)
(*     foo_setdisplay *)
(*   | If (ann, guard, then_, else_) -> *)
(*     foo_ite *)
(*   | Match (ann, scrut, branches) -> *)
(*     foo_match *)
(*   | Quantifier (_, _) -> *)
(*     foo_quantifier *)
(*   | SetComp _ -> *)
(*     foo_setcomp *)
(*   | StmtInExpr (_, _) -> *)
(*     foo_stmtinexpr *)
(*   | Let _ -> *)
(*     foo_let *)
(*   | MapComp _ -> *)
(*     foo_mapcomp *)
(*   | Lit _ -> *)
(*     foo_lit *)
(*   | This -> *)
(*     foo_this *)
(*   | Cardinality _ -> *)
(*     foo_cardinality *)
(*   | Tuple _ -> *)
(*     foo_tuple *)
(*   | Unary (_, _) -> *)
(*     foo_unary *)
(*   | Binary (_, _, _, _) -> *)
(*     foo_binary *)
(*   | Lemma _ -> *)
(*     foo_lemma *)

(* (\* and no_out_vars_expr_suffix *\) *)
(* (\*   (vars_out: AnnotationPass.TopDecl.formal_t list) *\) *)
(* (\*   (s: AnnotationPass.) *\) *)

(* let mode_expr_conjunct_funcall *)
(*     (vars_in:  AnnotationPass.TopDecl.formal_t list) *)
(*     (vars_out: AnnotationPass.TopDecl.formal_t list) *)
(*     (args: AnnotationPass.Prog.arglist_t) *)
(*     (ann: AnnotationMetaData.arglist_t) *)
(*   : ModePass.Prog.expr_t m = *)
(*   let (pos_args_in, pos_args_out, named_args_p) = begin *)
(*     let (part, named) = begin *)
(*       Util.partition_args_by_modes args *)
(*         (Option.map (function (_, modes) -> modes) ann) *)
(*     end in *)
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
