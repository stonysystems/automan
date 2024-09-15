(** Abstract syntax. *)

open Internal

module type MetaData = sig
  (* Use [@opaque] for instances where we don't want to / can't print this *)
  (* Toplevel declarations *)
  type predicate_decl_t    [@@deriving show, eq]
  type datatype_decl_t     [@@deriving show, eq]
  type synonym_type_decl_t [@@deriving show, eq]

  (* Types *)
  type type_t [@@deriving show, eq]

  (* Expressions *)
  type ite_t            [@@deriving show, eq]
  type match_t          [@@deriving show, eq]
  type quantification_t [@@deriving show, eq]
  type binary_op_t      [@@deriving show, eq]

  (* Expression suffixes *)
  type arglist_t [@@deriving show, eq]
end

module TrivMetaData : MetaData
  with type predicate_decl_t    = unit
  with type datatype_decl_t     = unit
  with type synonym_type_decl_t = unit

  with type type_t = unit

  with type ite_t            = unit
  with type match_t          = unit
  with type quantification_t = unit
  with type binary_op_t      = unit

  with type arglist_t = unit
= struct
  type predicate_decl_t    = unit [@@deriving show, eq]
  type datatype_decl_t     = unit [@@deriving show, eq]
  type synonym_type_decl_t = unit [@@deriving show, eq]

  type type_t = unit [@@deriving show, eq]

  type ite_t            = unit [@@deriving show, eq]
  type match_t          = unit [@@deriving show, eq]
  type quantification_t = unit [@@deriving show, eq]
  type binary_op_t      = unit [@@deriving show, eq]

  type arglist_t = unit [@@deriving show, eq]
end

type id_t   = string
[@@deriving show, eq]

(* Data that does not change during the different passes *)
module Common = struct
  (* Literals *)
  (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-literal-expression
     TODO: decimal literals *)
  type lit_t =
    | True | False | Null
    | Nat     of int
    | Char    of char
    | String  of string
  [@@deriving eq, show]

  (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#172753-basic-name-and-type-combinations *)
  type dotsuffix_t =
    | DSRequires | DSReads
    | DSId  of id_t
    | DSDig of int (* NOTE: natural number*)
  [@@deriving show, eq]

  (* a.b.c *)
  type member_qualified_name_t = id_t NonEmptyList.t
  [@@deriving show, eq]

  type uop_t = Neg | Not
  [@@deriving show, eq]

  type bop_t =
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-multiplication-expression *)
    | Mul | Div | Mod
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-addition-expression *)
    | Add | Sub
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-relational-expression
       NOTE: no hash calls *)
    | Eq | Neq | Lt | Gt | Lte | Gte | In | Nin | Disjoint
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-logical-expression *)
    | And | Or
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-implies-expression *)
    | Implies (* | Explies *) (* NOTE: treat explies as syntactic sugar *)
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-equivalence-expression *)
    | Equiv
  [@@deriving show, eq]

  (* Quantifications *)
  type quantifier_t = Forall | Exists
  [@@deriving show, eq]

  (* Topdecls (general) *)
  (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-declaration-modifier *)
  type topdecl_modifier_t =
    | Abstract | Ghost | Static | Opaque
  [@@deriving show, eq]

  (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-method-declaration
     NOTE: no constructor, twostate/least/greatest lemmas  *)
  type method_sort_t = Method | Lemma
  [@@deriving show, eq]

  (* Modules *)
  type module_reference_t =
    | Concrete | Abstract
  [@@deriving show, eq]

  type module_qualified_name_t = id_t NonEmptyList.t
  [@@deriving show, eq]

  (* Imports
     https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-importing-modules
     NOTE: no export sets *)
  type import_t =
    { opened: bool
    ; mref: (module_reference_t * id_t) option
    ; tgt: module_qualified_name_t
    }
  [@@deriving show, eq]
end

module AST (M : MetaData) = struct

  (** Types
      https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-types
  *)
  module Type = struct
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-type *)
    type name_seg_t = TpIdSeg of {id: id_t; gen_inst: t list }
    [@@deriving show, eq]

    (* NOTE: no function types *)
    and t =
      | TpName of M.type_t * name_seg_t NonEmptyList.t
      (* NOTE: this representation allows singleton tuples; use the smart
         constructor *)
      | TpTup  of t list
    [@@deriving show, eq]

    let simple_generic (id: id_t) (gen_inst: t list) (t_ann: M.type_t) =
      TpName (t_ann
             , NonEmptyList.singleton
                (TpIdSeg {id = id; gen_inst = gen_inst}))

    let simple (id: id_t) (t_ann: M.type_t): t = simple_generic id [] t_ann

    let int    = simple "int"
    let bool   = simple "bool"
    let nat    = simple "nat"
    let string = simple "string"
    let unit   = TpTup []

    let seq (elem: t) = simple_generic "seq" [elem]
    let set (elem: t) = simple_generic "set" [elem]
    let map (k: t) (v: t) = simple_generic "map" [k;v]

    (* formal parameters at the type level
       NOTE: no variance annotations *)
    type generic_params_t = id_t list
    [@@deriving show, eq]

    (* Smart constructor *)
    let tuple (tps: t list): t =
      match tps with
      | tp :: [] -> tp
      | _ -> TpTup tps

  end

  (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-augmented-dot-suffix
     NOTE: no hash calls *)
  type augmented_dotsuffix_t = Common.dotsuffix_t * Type.t list
  [@@deriving show, eq]

  (** Expressions
      https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-expressions
  *)
  module Prog = struct
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-name-segment
       https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-name-segment

       NOTE: no hash calls; if we add them, note we need ((Type.t
       NonEmptyList.t, hash_call) Either.t) option
    *)
    type name_seg_t = id_t * Type.t list
    [@@deriving show, eq]

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-case-pattern
       TODO: possibly *negated* literal expression
       NOTE: if we support disjunctive patterns, rename to
       "single_extended_pattern" *)
    type extended_pattern_t =
      | EPatLit  of Common.lit_t
      | EPatVar  of id_t * Type.t option
      (* NOTE: PatCtor (None, pats) means a tuple *)
      (* TODO: can the constructor identifier be qualified? *)
      | EPatCtor of id_t option * extended_pattern_t list
    [@@deriving eq, show]

    type pattern_t =
      | PatVar  of id_t * Type.t option
      | PatCtor of id_t option * pattern_t list
    [@@deriving eq, show]

    type expr_t =
      (* primary expressions:
         https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-primary-expression *)
      | Suffixed of expr_t * suffix_t
      (*  - name segment expressions **)
      | NameSeg of name_seg_t

      (* - lambda expressions
           https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-lambda-expression
           TODO: lambda_spec? *)
      | Lambda  of (id_t * Type.t option) list * expr_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-map-display-expression
         NOTE: no imap *)
      | MapDisplay of (expr_t * expr_t) list
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-seq-comprehension *)
      | SeqDisplay of seq_display_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-set-display-expression
         NOTE: no multiset, multiset from sequence *)
      | SetDisplay of expr_t list

      (* primary: endless
         https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-endless-expression *)
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-if-expression
         NOTE: no binding guards*)
      | If of M.ite_t * expr_t * expr_t * expr_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-match-expression *)
      | Match of M.match_t * expr_t * case_expr_t list
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-quantifier-expression
         NOTE: Dafny 3 does not support per-variable quantifier ranges, so we
         aren't either *)
      | Quantifier of M.quantification_t * quantification_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-set-comprehension-expression
         NOTE: no support for iset
         NOTE: no per-variable quantifier ranges *)
      | SetComp of set_comp_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-statement-in-expression
         NOTE: that an expression follows the statement is part of the endless expression definition *)
      | StmtInExpr of stmt_in_expr_t * expr_t
      (* | ... *)
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-let-expression
         NOTE: no let-fail, assign-such-that *)
      | Let of
          { ghost: bool
          ; pats: pattern_t NonEmptyList.t
          ; defs: expr_t NonEmptyList.t
          ; body: expr_t }
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-map-comprehension-expression
         NOTE: imap not supported *)
      | MapComp of map_comp_t
      (* const atom expressions: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-atomic-expression
         NOTE: no fresh, allocated, unchanged, old *)
      | Lit  of Common.lit_t
      | This
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-cardinality-expression
         NOTE: previously ExprLen *)
      | Cardinality of expr_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-parenthesized-expression
         NOTE: no ghost components, no by-name bindings
         NOTE: this should never be a singleton list (but it could be empty) *)
      | Tuple of expr_t list

      (* unary expressions: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-unary-expression *)
      | Unary of Common.uop_t * expr_t
      (* NOTE: the following are unsupported
         - as/is: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-as-is-expression
         - bitvector: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-bitvector-expression
      *)
      | Binary of M.binary_op_t * Common.bop_t * expr_t * expr_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-top-level-expression *)
      | Lemma of {lem: expr_t; e: expr_t}
    [@@deriving show, eq]

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-statements *)
    (* NOTE: no labeled statements, break, calc, expect, forall, modify,
       print, reveal, update-and-call[havoc, such-that], update-failure,
       while, for-loop, yield
    *)
    and stmt_t =
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-assert-statement *)
      | SAssert of stmt_assert_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-assume-statement *)
      | SAssume of stmt_assume_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-block-statement *)
      | SBlock  of stmt_block_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-if-statement
         NOTE: no alternative blocks*)
      | SIf of stmt_if_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-match-statement *)
      | SMatch of expr_t * stmt_case_t list
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-return-statement
         NOTE: RHS is limited to expressions with (possibly 0) attributes *)
      | SReturn of rhs_t list
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-update-and-call-statement
         Update And Call:
         TODO: if there's only one lhs, it may come with attributes; otherwise, none have attributes
      *)
      | SUpdAndCall of lhs_t NonEmptyList.t * rhs_t list
      (* | SCall of expr_t * suffix_t list * attribute_t list *)
      (* (\* - Update variant: assignments 1-1, 1-many, many-1, many-many *)
      (*      NOTE: no havoc or such-that assignments *\) *)
      (* | SUpdAssign of lhs_t NonEmptyList.t * rhs_t NonEmptyList.t *)

      | SVarDecl of var_decl_t
    [@@deriving show, eq]

    (* NOTE: no expect, reveal, calc *)
    and stmt_in_expr_t =
      | Assert of stmt_assert_t
      | Assume of stmt_assume_t

    and stmt_assert_t = attribute_t list * (* label_name * *) expr_t * stmt_block_t
    and stmt_assume_t = attribute_t list * expr_t
    and stmt_block_t  = stmt_t list

    (* NOTE: no alternative block, binding guard *)
    and stmt_if_t = { guard: expr_t; then_br: stmt_block_t; footer: stmt_if_footer_t option }
    and stmt_if_footer_t =
      | ElseIf    of stmt_if_t
      | ElseBlock of stmt_block_t
      (* | AlternativeBlock *)

    and stmt_case_t = extended_pattern_t * stmt_t list

    (** Suffixes
        https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-suffix
    *)
    and suffix_t =
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-augmented-dot-suffix *)
      | AugDot   of augmented_dotsuffix_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-datatype-update-suffix *)
      | DataUpd  of member_binding_upd_t NonEmptyList.t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-subsequence-suffix *)
      | Subseq   of subseq_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-subsequence-slices-suffix *)
      | SliceLen of {sublens: expr_t NonEmptyList.t; to_end: bool }
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-sequence-update-suffix
         NOTE: The grammar says there's only one update, but the example shows
         multiple *)
      | SeqUpd   of {idx: expr_t; v: expr_t}
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-selection-suffix
         NOTE: multiple indices (for multi-dimensional arrays) not (yet?) supported *)
      | Sel      of expr_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-argument-list-suffix *)
      | ArgList  of arglist_t * M.arglist_t
    [@@deriving show, eq]

    and subseq_t = {lb: expr_t option; ub: expr_t option}

    and member_binding_upd_t = (id_t, int) Either.t * expr_t

    and arglist_t =
      { positional: expr_t list
      ; named: (id_t * expr_t) list }

    and seq_display_t =
      | SeqEnumerate of expr_t list
      | SeqTabulate  of
          { gen_inst: Type.t list
          ; len: expr_t
          ; func: expr_t
          }

    and quantification_t =
      { qt: Common.quantifier_t
      ; qdom: qdom_t
      ; qbody: expr_t }

    and map_comp_t =
      { qdom: qdom_t
      ; key: expr_t option
      ; valu: expr_t }

    and set_comp_t =
      { qdom: qdom_t
      ; body: expr_t option }

    and attribute_t = string * expr_t list

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-case-pattern
       NOTE: disjunctive patterns unsupported *)
    and case_expr_t =
        Case of attribute_t list * extended_pattern_t * expr_t

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-quantifier-expression *)
    and qvar_decl_t =
        QVar of id_t * Type.t option * expr_t option * attribute_t list

    and qdom_t =
        QDom of {qvars: qvar_decl_t list; qrange: expr_t option}

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-lhs-expression NOTE:
       confusingly, the Dafny manual refers to both the definiendum of an
       assignment *and* to the expressions that can be assigned values! *)
    (* NOTE: no constatom expressions (in particular, old) *)
    and lhs_t = expr_t

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-rhs-expression
       NOTE: no array/object allocations, havoc rhs *)
    and rhs_t = expr_t * attribute_t list

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-variable-declaration-statement *)
    and var_decl_t =
      | DeclIds of var_decl_id_lhs_t list * var_decl_ids_rhs_t option

    and var_decl_id_lhs_t = { id: id_t; tp: Type.t option; attrs: attribute_t list }

    (* NOTE: no update-failure, such-that *)
    and var_decl_ids_rhs_t =
      | Assign of rhs_t list

    (** Smart constructor for Tuple *)
    let tuple (es: expr_t list): expr_t =
      match es with
      | e :: [] -> e
      | _ -> Tuple es

    (** should only be called with relational operators that support chaining,
        and can be chained together *)
    let rec chain_bop
        (and_ann: M.binary_op_t) (e1: expr_t)
        (es: (M.binary_op_t * Common.bop_t * expr_t) list)
      : expr_t =
      match es with
      | [] -> e1
      | [(ann, o, e2)] -> Binary (ann, o, e1, e2)
      | (ann, o, e2) :: es ->
        let res = chain_bop and_ann e2 es in
        Binary (and_ann, And, Binary (ann, o, e1, e2), res)

    let rec to_conjuncts (e: expr_t): expr_t list =
      match e with
      | Binary (_, Common.And, e1, e2) ->
        to_conjuncts e1 @ to_conjuncts e2
      | _ ->
        [e]

    let assoc_right_bop
        (o_ann: M.binary_op_t) (o: Common.bop_t)
        (es: expr_t NonEmptyList.t)
      : expr_t =
      NonEmptyList.fold_right_1
        (fun x y -> Binary (o_ann, o, x, y))
        es

    let rec assoc_right_bop_ann
        (o: Common.bop_t) (es: (expr_t * 'a) list)
        (ann: 'a -> 'a -> M.binary_op_t * 'a)
        (neutral: expr_t * 'a) =
      match es with
      | [] -> neutral
      | [(e, a)] ->
        let (a', x) = ann a (snd neutral) in
        (Binary (a', o, e, fst neutral), x)
      | (e1, a1) :: (e2, a2) :: [] ->
        let (a', x) = ann a1 a2 in
        (Binary (a', o, e1, e2), x)
      | (e1, a1) :: es ->
        let (e2, a2) = assoc_right_bop_ann o es ann neutral in
        let (a', x) = ann a1 a2 in
        (Binary (a', o, e1, e2), x)

    let foldl1 (f: expr_t -> expr_t -> expr_t) (es: expr_t list): expr_t =
      match es with
      | [] -> assert false      (* TODO: better error handling (integrate with parser (option)) *)
      | init :: es ->
        List.fold_left f init es

    let maybe_to_id (e: expr_t): id_t option =
      match e with
      | NameSeg (id, []) -> Some id
      | _ -> None

    let maybe_to_qualified_id (e: expr_t): id_t NonEmptyList.t option =
      (* TODO: handle identifier dot suffixes with generic instantations *)
      let rec aux accum = function
        | NameSeg (id, []) ->
          Some (id :: accum)
        | Suffixed (e', AugDot (Common.DSId id, [])) ->
          aux (id :: accum) e'
        | _ -> None
      in
      Option.map NonEmptyList.coerce (aux [] e)

    let from_qualified_id (qid: id_t NonEmptyList.t): expr_t =
      let NonEmptyList.( :: ) (hd, tl) = qid in
      List.fold_left
        (fun qid id -> Suffixed (qid, AugDot (Common.DSId id, [])))
        (NameSeg (hd, [])) tl

    (* Argument lists *)
    type pseudo_arglist_t = (expr_t * expr_t option) list
    [@@deriving show, eq]

    let coerce_arglist (args: pseudo_arglist_t): arglist_t =
      let here = "Syntax.AST.ArgList.coerce: " in
      let rec aux_name acc_pos acc_name = function
        | [] -> (acc_pos, acc_name)
        | (expr_id, Some expr_arg) :: args ->
          begin
            match maybe_to_id expr_id with
            | None ->
              failwith begin
                here
                ^ "invalid parameter name: " ^ (show_expr_t expr_id)
              end
            | Some id ->
              aux_name acc_pos ((id, expr_arg) :: acc_name) args
          end
        | _ :: _ ->
          failwith (here ^ "positional arguments must come before named ones")
      in
      let rec aux acc_pos = function
        | [] -> (acc_pos, [])
        | (expr, None) :: args ->
          aux (expr :: acc_pos) args
        | _ :: _ as args ->
          aux_name acc_pos [] args
      in
      let (positional, named) = aux [] args in
      { positional = List.rev positional
      ; named      = List.rev named }
  end

  module TopDecl = struct

    (* Formal parameters to constructors/functions/methods *)
    type formal_t = Formal of id_t * Type.t
    [@@deriving show, eq]

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-datatype
       NOTE: no codatatype, type members
       NOTE: constructor argument names required *)
    (* corresponds to DatatypeMemberDecl *)
    type datatype_ctor_t =
      DataCtor of Prog.attribute_t list * id_t * formal_t list
    [@@deriving show, eq]

    type datatype_t =
      M.datatype_decl_t
      * Prog.attribute_t list
      * id_t * Type.generic_params_t
      * datatype_ctor_t NonEmptyList.t
    [@@deriving show, eq]

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-type-definition
       NOTE: no type parameter characteristics, witness clauses *)
    type synonym_type_rhs_t =
      | Synonym of Type.t
      | Subset  of id_t * Type.t option * Prog.expr_t
    [@@deriving show, eq]

    type synonym_type_t =
      { ann: M.synonym_type_decl_t
      ; attrs: Prog.attribute_t list
      ; id: id_t
      ; params: Type.generic_params_t
      ; rhs: synonym_type_rhs_t
      }
    [@@deriving show, eq]

    (* Functions/Predicates START
       https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-function-declaration
       NOTE: no twostate, least/greatest on predicates
       NOTE: Dafny 4 obsolesced "function method", but we are targetting
             Dafny 3 *)
    type function_spec_t =
      | Requires    of Prog.expr_t
      | Reads       of Prog.expr_t
      | Ensures     of Prog.expr_t
      | Decreases   of Prog.expr_t
    [@@deriving show, eq]

    type function_t =
      | Predicate of
          M.predicate_decl_t
          * bool                  (* method present *)
          * Prog.attribute_t list * id_t
          * Type.generic_params_t * formal_t list
          * function_spec_t list
          * Prog.expr_t
      | Function of
          bool                  (* method present *)
          * Prog.attribute_t list * id_t
          * Type.generic_params_t * formal_t list * Type.t
          * function_spec_t list
          * Prog.expr_t
    [@@deriving show, eq]
    (* Functions/predicates END *)

    (* Method/Lemma START
       https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-method-declaration
       NOTE: no constructor, twostate/least/greatest lemmas *)

    (* NOTE: no KType, "returns" clause *)
    type method_signature_t =
      { generic_params: Type.generic_params_t
      ; params: formal_t list
      }
    [@@deriving show, eq]

    type method_spec_t =
      | MModifies  of Prog.expr_t
      | MRequires  of Prog.expr_t
      | MEnsures   of Prog.expr_t
      | MDecreases of Prog.expr_t
    [@@deriving show, eq]

    type method_t =
      { sort: Common.method_sort_t
      ; attrs: Prog.attribute_t list
      ; id: id_t
      ; signature: method_signature_t
      ; spec: method_spec_t list
      ; body: Prog.stmt_block_t }
    [@@deriving show, eq]
    (* Method/Lemma END *)

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-top-level-declaration *)
    type t = Common.topdecl_modifier_t list * t'
    [@@deriving show, eq]

    (* NOTE: no ClassDecl, NewtypeDecl, SynonymTypeDecl(OpaqueTypeDecl_),
       ModuleExport, class field or constant *)
    and t' =
      | ModuleImport    of Common.import_t
      | ModuleDef       of module_def_t
      (* | ClassDecl *)
      | DatatypeDecl    of datatype_t
      | SynonymTypeDecl of synonym_type_t
      | PredFunDecl     of function_t
      | MethLemDecl     of method_t
    [@@deriving show, eq]

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-module-definition
       NOTE: no /declaring/ modules with qualified names (use case?)
       NOTE: no "refines" *)
    and module_def_t = Prog.attribute_t list * id_t * t list
    (*                                         ^ module_qualified_name_t *)
  end

  type t =
    | Dafny of
        { includes: id_t list
        ; decls: TopDecl.t list
        }
  [@@deriving show, eq]
end

module ParserPass     = AST (TrivMetaData)

module Convert (M1 : MetaData) (M2 : MetaData) = struct
  module Src = AST (M1)
  module Tgt = AST (M2)

  type attr_handler_t =
    Src.Prog.attribute_t list -> Tgt.Prog.attribute_t list

  type tp_handler_t =
    M1.type_t -> M2.type_t

  let rec typ (tp_h: tp_handler_t) (tp: Src.Type.t) : Tgt.Type.t =
    match tp with
    | TpTup tps -> TpTup (List.map (typ tp_h) tps)
    | TpName (t_ann, nss) ->
      TpName
        ( tp_h t_ann
        , NonEmptyList.map (typ_name_seg tp_h) nss)

  and typ_name_seg (tp_h: tp_handler_t) (nsegs: Src.Type.name_seg_t)
    : Tgt.Type.name_seg_t =
    let TpIdSeg {id = id; gen_inst = gen_inst} = nsegs in
    TpIdSeg {id = id; gen_inst = List.map (typ tp_h) gen_inst}

  let rec extended_pattern
      (tp_h: tp_handler_t) (pat: Src.Prog.extended_pattern_t)
    : Tgt.Prog.extended_pattern_t =
    match pat with
    | EPatLit lit -> EPatLit lit
    | EPatVar (id, tp) ->
      EPatVar (id, Option.map (typ tp_h) tp)
    | EPatCtor (id, pats) ->
      EPatCtor (id, List.map (extended_pattern tp_h) pats)

  let rec pattern
      (tp_h: tp_handler_t) (pat: Src.Prog.pattern_t)
    : Tgt.Prog.pattern_t =
    match pat with
    | PatVar (id, tp) -> PatVar (id, Option.map (typ tp_h) tp)
    | PatCtor (id, pats) -> PatCtor (id, List.map (pattern tp_h) pats)

  let lambda_params
      (tp_h: tp_handler_t) (ps: (id_t * Src.Type.t option) list)
    : (id_t * Tgt.Type.t option) list =
    List.map (function (p, tp) -> (p, Option.map (typ tp_h) tp)) ps

end

module Erase (M: MetaData) = struct
  module C = Convert (TrivMetaData) (M)
  module Src = AST (M)

  let rec typ (tp: Src.Type.t): ParserPass.Type.t =
    match tp with
    | TpName (_, segs) ->
      let tp_name_seg (tp_seg: Src.Type.name_seg_t): ParserPass.Type.name_seg_t =
        let TpIdSeg {id = id; gen_inst = tp_args} = tp_seg in
        let tp_args' = List.map typ tp_args in
        TpIdSeg {id = id; gen_inst = tp_args'}
      in
      let segs' = NonEmptyList.map tp_name_seg segs in
      TpName ((), segs')
    | TpTup tps ->
      let tps' = List.map typ tps in
      TpTup tps'

  let rec expr (e: Src.Prog.expr_t): ParserPass.Prog.expr_t =
    match e with
    | Suffixed (e_pref, e_suff) ->
      let e_pref' = expr e_pref in
      let e_suff' = suffix e_suff in
      ParserPass.Prog.Suffixed (e_pref', e_suff')
    | NameSeg (id, tp_args) ->
      let tp_args' = List.map typ tp_args in
      NameSeg (id, tp_args')
    | Lambda (ps, body) ->
      let (ps', body') =
        ( List.map
            (function (id, tp_opt) -> (id, Option.map typ tp_opt))
            ps
        , expr body)
      in
      Lambda (ps', body')
    | MapDisplay kvs ->
      let kvs' =
        List.map (function (k, v) -> (expr k, expr v)) kvs in
      MapDisplay kvs'
    | SeqDisplay sdisp ->
      let sdisp' =
        begin
          match sdisp with
          | SeqEnumerate es ->
            let es' = List.map expr es in
            ParserPass.Prog.SeqEnumerate es'
          | SeqTabulate {gen_inst = tp_args; len = len; func = func} ->
            let (tp_args', len', func') =
              ( List.map typ tp_args
              , expr len
              , expr func )
            in
            ParserPass.Prog.SeqTabulate
              { gen_inst = tp_args'
              ; len = len'
              ; func = func' }
        end
      in
      SeqDisplay sdisp'
    | SetDisplay elems ->
      let elems' = List.map expr elems in
      SetDisplay elems'
    | If (_, g, t, e) ->
      let (g', t', e') = (expr g, expr t, expr e) in
      ParserPass.Prog.If ((), g', t', e')
    | Match (_, scrut, branches) ->
      let (scrut', branches') =
        ( expr scrut
        , List.map
            (function Src.Prog.Case (_, e_pat, body) ->
               let (attrs', e_pat', body') =
                 ([], extended_pattern e_pat, expr body) in
               ParserPass.Prog.Case (attrs', e_pat', body'))
            branches )
      in
      Match ((), scrut', branches')
    | Quantifier (_, q) ->
      let (qdom', qbody') = (qdom q.qdom, expr q.qbody) in
      Quantifier ((), {qt = q.qt; qdom = qdom'; qbody = qbody'})
    | SetComp scomp ->
      let (qdom', body') = (qdom scomp.qdom, Option.map expr scomp.body) in
      SetComp {qdom = qdom'; body = body'}
    | StmtInExpr (st, e) ->
      let stmt' = begin
        match st with
        | Assert (_attrs, assrt, by_block) ->
          let assrt' = expr assrt in
          let by_block' = List.map stmt by_block in
          ParserPass.Prog.Assert ([], assrt', by_block')
        | Assume (_attrs, assme) ->
          let assme' = expr assme in
          ParserPass.Prog.Assume([], assme')
      end in
      let e' = expr e in
      StmtInExpr (stmt', e')
    | Let {ghost = ghost; pats = pats; defs = defs; body = body} ->
      let (pats', defs', body') =
        ( NonEmptyList.map pattern pats
        , NonEmptyList.map expr defs
        , expr body )
      in
      ParserPass.Prog.Let
        { ghost = ghost
        ; pats = pats'
        ; defs = defs'
        ; body = body' }
    | MapComp mcomp ->
      let (qdom', key', valu') =
        ( qdom mcomp.qdom
        , Option.map expr mcomp.key
        , expr mcomp.valu )
      in
      MapComp {qdom = qdom'; key = key'; valu = valu'}
    | Lit l ->
      Lit l
    | This ->
      ParserPass.Prog.This
    | Cardinality e ->
      let e' = expr e in
      Cardinality e'
    | Tuple comps ->
      let comps' = List.map expr comps in
      Tuple comps'
    | Unary (op, e) ->
      let e' = expr e in
      Unary (op, e')
    | Binary (_, op, e1, e2) ->
      let (e1', e2') = (expr e1, expr e2) in
      Binary ((), op, e1', e2')
    | Lemma l ->
      let (lem', body') = (expr l.lem, expr e) in
      Lemma {lem = lem'; e = body'}

  and stmt (s: Src.Prog.stmt_t): ParserPass.Prog.stmt_t =
    match s with
    | SAssert (_, assertion, by_block) ->
      let assertion' = expr assertion in
      let by_block' = List.map stmt by_block in
      SAssert ([], assertion', by_block')
    | SAssume (_, assumption) ->
      let assumption' = expr assumption in
      SAssume ([], assumption')
    | SBlock sblock ->
      let sblock' = List.map stmt sblock in
      SBlock sblock'
    | SIf sif ->
      let rec stmt_if (s: Src.Prog.stmt_if_t): ParserPass.Prog.stmt_if_t =
        let Src.Prog.({guard = g; then_br = t; footer = e}) = s in
        let g' = expr g in
        let t' = List.map stmt t in
        let e' =
          Option.map
            (function
              | Src.Prog.ElseIf sub_s ->
                ParserPass.Prog.ElseIf (stmt_if sub_s)
              | Src.Prog.ElseBlock e_block ->
                ParserPass.Prog.ElseBlock (List.map stmt e_block))
            e
        in
        ParserPass.Prog.({guard = g'; then_br = t'; footer = e'})
      in
      let sif' = stmt_if sif in
      SIf sif'
    | SMatch (scrut, tree) ->
      let scrut' = expr scrut in
      let tree' =
        List.map
          (function (e_pat, stmts) ->
             let e_pat' = extended_pattern e_pat in
             let stmts' = List.map stmt stmts in
             (e_pat', stmts'))
          tree
      in
      SMatch (scrut', tree')
    | SReturn rets ->
      (* NOTE: this has to change if we want to support more rhs kinds *)
      let rets' = List.map (function (e, _) -> (expr e, [])) rets in
      SReturn rets'
    | SUpdAndCall (lhss, rhss) ->
      let lhss' = NonEmptyList.map expr lhss in
      let rhss' = List.map (function (e, _) -> (expr e, [])) rhss in
      SUpdAndCall (lhss', rhss')
    | SVarDecl (DeclIds (vars, rhss)) ->
      let vars' =
        List.map
          (function Src.Prog.({id = id; tp = tp_opt; attrs = _}) ->
             let tp_opt' = Option.map typ tp_opt in
             ParserPass.Prog.({id = id; tp = tp_opt'; attrs = []}))
          vars
      in
      let rhss' =
        Option.map (function
            | Src.Prog.Assign rhss ->
              let rhss' =
                List.map (function (rhs, _) -> (expr rhs, [])) rhss in
              ParserPass.Prog.Assign rhss')
          rhss
      in
      SVarDecl (DeclIds (vars', rhss'))

  and suffix (s: Src.Prog.suffix_t): ParserPass.Prog.suffix_t =
    match s with
    | AugDot (dotsuff, tp_args) ->
      let tp_args' = List.map typ tp_args in
      AugDot (dotsuff, tp_args')
    | DataUpd upd ->
      let upd' =
        NonEmptyList.map
          (function (mem, vlu) ->
             let vlu' = expr vlu in
             (mem, vlu'))
          upd
      in
      DataUpd upd'
    | Subseq {lb = lb; ub = ub} ->
      let lb' = Option.map expr lb in
      let ub' = Option.map expr ub in
      Subseq {lb = lb'; ub = ub'}
    | SliceLen {sublens = sublens; to_end = to_end} ->
      let sublens' = NonEmptyList.map expr sublens in
      SliceLen {sublens = sublens'; to_end = to_end}
    | SeqUpd {idx = idx; v = v} ->
      let idx' = expr idx in
      let v' = expr v in
      SeqUpd {idx = idx'; v = v'}
    | Sel e ->
      let e' = expr e in
      Sel e'
    | ArgList ({positional = pos; named = nam}, _ann) ->
      let pos' = List.map expr pos in
      let nam' = List.map (function (id, e) -> (id, expr e)) nam in
      ArgList ({positional = pos'; named = nam'}, ())

  and pattern (pat: Src.Prog.pattern_t): ParserPass.Prog.pattern_t =
    match pat with
    | PatVar (id, tp_opt) ->
      let tp_opt' = Option.map typ tp_opt in
      PatVar (id, tp_opt')
    | PatCtor (id_opt, pats) ->
      let pats' = List.map pattern pats in
      PatCtor (id_opt, pats')

  and extended_pattern(epat: Src.Prog.extended_pattern_t)
    : ParserPass.Prog.extended_pattern_t =
    match epat with
    | EPatLit l ->
      EPatLit l
    | EPatVar (id, tp_opt) ->
      let tp_opt' = Option.map typ tp_opt in
      EPatVar (id, tp_opt')
    | EPatCtor (ctor, epats) ->
      let epats' = List.map extended_pattern epats in
      EPatCtor (ctor, epats')

  and qdom (qdom: Src.Prog.qdom_t): ParserPass.Prog.qdom_t =
    let qvar_decl (qvar: Src.Prog.qvar_decl_t): ParserPass.Prog.qvar_decl_t =
      let Src.Prog.QVar (id, tp_opt, coll_opt, _) = qvar in
      let (tp_opt', coll_opt', attrs') =
        ( Option.map typ tp_opt
        , Option.map expr coll_opt
        , [] )
      in
      ParserPass.Prog.QVar (id, tp_opt', coll_opt', attrs')
    in

    let Src.Prog.QDom qd = qdom in
    let (qvars', qrange') =
      (List.map qvar_decl qd.qvars, Option.map expr qd.qrange) in
    ParserPass.Prog.QDom {qvars = qvars'; qrange = qrange'}
end

(* AutoMan annotations *)
module Annotation = struct
  type mode_t = Input | Output
  [@@deriving show, eq]

  type t =
    | Module    of module_t
    | Predicate of predicate_t
    | TypeAlias of tp_alias_t
  [@@deriving show, eq]

  and predicate_t = id_t * mode_t list
  and module_t = id_t * t list
  and tp_alias_t = id_t * ParserPass.Type.t

  type qualified_tp_alias_t = Common.module_qualified_name_t * ParserPass.Type.t
  [@@deriving show, eq]

  type toplevel_t = t list
  [@@deriving show, eq]

  let filter_by_module_id (id: id_t) (anns: toplevel_t) =
    List.filter
      (function
        | Module (m_id, _) -> m_id = id
        | _ -> false)
      anns

  let filter_by_predicate_id (id: id_t) (anns: toplevel_t) =
    List.filter
      (function
        | Predicate (p_id, _) -> p_id = id
        | _ -> false)
      anns

  let filter_by_tp_alias_tgt
      (tp: ParserPass.Type.t) (anns: toplevel_t)
    : toplevel_t =
    List.filter
      (function
        | TypeAlias (_, tp') -> tp = tp'
        | _ -> false)
      anns

end
