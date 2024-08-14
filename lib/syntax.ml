(** Abstract syntax. *)

open Internal

module type MetaData = sig
  (* Use [@opaque] for instances where we don't want to / can't print this *)
  type predicate_decl_t [@@deriving show, eq]
  type arglist_t [@@deriving show, eq]
end

module TrivMetaData : MetaData
  with type predicate_decl_t  = unit
  with type arglist_t = unit
= struct
  type predicate_decl_t  = unit [@@deriving show, eq]
  type arglist_t = unit [@@deriving show, eq]
end

type id_t   = string
[@@deriving show, eq]

(* AutoMan annotations *)
module Annotation = struct
  type mode_t = Input | Output
  [@@deriving show, eq]

  type t =
    | Module    of module_t
    | Predicate of predicate_t
  [@@deriving show, eq]

  and predicate_t = id_t * mode_t list

  and module_t = id_t * t list

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
end

module AnnotationMetaData : MetaData
  with type predicate_decl_t  = Annotation.mode_t list option
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

  (** - When this is Option.None, the call is not associated with a known
        predicate. For now, assume this means all arguments are input moded

      - When this is Option.Some, the mode list this contains has the same
        length as the argument list suffix, and the expression to which the
        call is attached is given the qualified identifier
  *)
  type arglist_t = (id_t NonEmptyList.t * Annotation.mode_t list) option
  [@@deriving show, eq]
end

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

  (* Quantifiers *)
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
      | TpName of name_seg_t NonEmptyList.t
      (* NOTE: this representation allows singleton tuples; use the smart
         constructor *)
      | TpTup  of t list
    [@@deriving show, eq]

    let simple_generic (id: id_t) (gen_inst: t list) =
      TpName (NonEmptyList.singleton
                (TpIdSeg {id = id; gen_inst = gen_inst}))

    let simple (id: id_t): t = simple_generic id []

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
      | If of expr_t * expr_t * expr_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-match-expression *)
      | Match of expr_t * case_expr_t list
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-quantifier-expression
         NOTE: Dafny 3 does not support per-variable quantifier ranges, so we
         aren't either *)
      | Quantifier of
          { qt : Common.quantifier_t
          ; qdom : qdom_t
          ; qbody : expr_t }
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-set-comprehension-expression
         NOTE: no support for iset
         NOTE: no per-variable quantifier ranges *)
      | SetComp of qdom_t * expr_t option
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
      | MapComp of { qdom: qdom_t; key: expr_t option; valu: expr_t }
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
      | Binary of Common.bop_t * expr_t * expr_t
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
      | Subseq   of {lb: expr_t option; ub: expr_t option}
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
    let rec chain_bop (e1: expr_t) (es: (Common.bop_t * expr_t) list): expr_t =
      match es with
      | [] -> e1
      | [(o, e2)] -> Binary (o, e1, e2)
      | (o, e2) :: es ->
        let res = chain_bop e2 es in
        Binary (And, Binary (o, e1, e2), res)

    let assoc_right_bop (o: Common.bop_t) (es: expr_t NonEmptyList.t): expr_t =
      NonEmptyList.fold_right_1 (fun x y -> Binary (o, x, y)) es

    let foldl1 (f: expr_t -> expr_t -> expr_t) (es: expr_t list): expr_t =
      match es with
      | [] -> assert false      (* TODO: better error handling (integrate with parser (option)) *)
      | init :: es ->
        List.fold_left f init es

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
    type pseudo_arglist_t = (id_t option * expr_t) list
    [@@deriving show, eq]

    let coerce_arglist (args: pseudo_arglist_t): arglist_t =
      let rec aux_name acc_pos acc_name = function
        | [] -> (acc_pos, acc_name)
        | (Some id, expr) :: args ->
          aux_name acc_pos ((id, expr) :: acc_name) args
        | _ :: _ ->
          failwith
            "Syntax.AST.ArgList.coerce: positional arguments must come before named ones"
      in
      let rec aux acc_pos = function
        | [] -> (acc_pos, [])
        | (None, expr) :: args ->
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
      Prog.attribute_t list
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
      { attrs: Prog.attribute_t list
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

module Convert (M1 : MetaData) (M2 : MetaData) = struct
  module Src = AST (M1)
  module Tgt = AST (M2)

  type attr_handler_t =
    Src.Prog.attribute_t list -> Tgt.Prog.attribute_t list

  let rec typ (tp: Src.Type.t): Tgt.Type.t =
    let aux_ns (ns: Src.Type.name_seg_t): Tgt.Type.name_seg_t =
      let TpIdSeg {id = id; gen_inst = gen_inst} = ns in
      TpIdSeg {id = id; gen_inst = List.map typ gen_inst}
    in
    match tp with
    | TpTup tps -> TpTup (List.map typ tps)
    | TpName nss -> TpName (NonEmptyList.map aux_ns nss)

  let rec extended_pattern (pat: Src.Prog.extended_pattern_t)
    : Tgt.Prog.extended_pattern_t =
    match pat with
    | EPatLit lit -> EPatLit lit
    | EPatVar (id, tp) ->
      EPatVar (id, Option.map typ tp)
    | EPatCtor (id, pats) ->
      EPatCtor (id, List.map extended_pattern pats)

  let rec pattern (pat: Src.Prog.pattern_t): Tgt.Prog.pattern_t =
    match pat with
    | PatVar (id, tp) -> PatVar (id, Option.map typ tp)
    | PatCtor (id, pats) -> PatCtor (id, List.map pattern pats)

  let formal (p: Src.TopDecl.formal_t): Tgt.TopDecl.formal_t =
    let Formal (id, tp) = p in
    Formal (id, typ tp)

  let method_signature (s: Src.TopDecl.method_signature_t)
    : Tgt.TopDecl.method_signature_t =
    let ps = List.map formal s.params in
    { generic_params = s.generic_params; params = ps }

  let datatype_ctor (attr_handler: attr_handler_t) (ctor: Src.TopDecl.datatype_ctor_t)
    : Tgt.TopDecl.datatype_ctor_t =
    let DataCtor (attrs, id, params) = ctor in
    DataCtor (attr_handler attrs, id, List.map formal params)

  let datatype (attr_handler: attr_handler_t) (d: Src.TopDecl.datatype_t)
    : Tgt.TopDecl.datatype_t =
    let (attrs, id, tpparams, ctors) = d in
    (attr_handler attrs, id, tpparams
    , NonEmptyList.map (datatype_ctor attr_handler) ctors)

  let synonym_typ_rhs (rhs: Src.TopDecl.synonym_type_rhs_t)
    : Tgt.TopDecl.synonym_type_rhs_t =
    match rhs with
    | Synonym tp -> Tgt.TopDecl.Synonym (typ tp)
    | Subset (_, _, _) ->
      failwith ("TODO: subset types: " ^ Src.TopDecl.(show_synonym_type_rhs_t rhs))

  let synonym_type (attr_handler: attr_handler_t) (d: Src.TopDecl.synonym_type_t)
    : Tgt.TopDecl.synonym_type_t =
    { attrs = attr_handler d.attrs
    ; id = d.id
    ; params = d.params
    ; rhs = synonym_typ_rhs d.rhs
    }
end

module ParserPass     = AST (TrivMetaData)
module AnnotationPass = AST (AnnotationMetaData)
