(** Abstract syntax. *)

open Internal

module type MetaData = sig
  (* Use [@opaque] for instances where we don't want to / can't print this *)
  type predicate_t [@@deriving show]
end

module TrivMetaData : MetaData
  with type predicate_t = unit
= struct
  type predicate_t = unit [@@deriving show]
end

type id_t   = string
[@@deriving show, eq]

(* https://dafny.org/dafny/DafnyRef/DafnyRef.html#172753-basic-name-and-type-combinations *)
type dotsuffix_t =
  | DSRequires | DSReads
  | DSId  of id_t
  | DSDig of int (* NOTE: natural number*)
[@@deriving show, eq]

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
      (* NOTE: this representation allows singleton tuples *)
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

  end

  (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-augmented-dot-suffix
     NOTE: no hash calls *)
  type augmented_dotsuffix_t = dotsuffix_t * Type.t list
  [@@deriving show, eq]

  (** Expressions
      https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-expressions
  *)
  module Prog = struct
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-literal-expression
       TODO: decimal literals *)
    type lit_t =
      | True | False | Null
      | Nat     of int
      | Char    of char
      | String  of string
    [@@deriving eq, show]

    type quantifier_t = Forall | Exists
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
      | EPatLit  of lit_t
      | EPatVar  of id_t * Type.t option
      (* NOTE: PatCtor (None, pats) means a tuple *)
      (* TODO: can the constructor identifier be qualified? *)
      | EPatCtor of id_t option * extended_pattern_t list
    [@@deriving eq, show]

    type pattern =
      | PatVar  of id_t * Type.t option
      | PatCtor of id_t option * pattern list
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
          { qt : quantifier_t
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
          ; pats: pattern NonEmptyList.t
          ; def: expr_t NonEmptyList.t
          ; body: expr_t }
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-map-comprehension-expression
         NOTE: imap not supported *)
      | MapComp of { qdom: qdom_t; key: expr_t option; valu: expr_t }
      (* const atom expressions: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-atomic-expression
         NOTE: no fresh, allocated, unchanged, old *)
      | Lit  of lit_t
      | This
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-cardinality-expression
         NOTE: previously ExprLen *)
      | Cardinality of expr_t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-parenthesized-expression
         NOTE: no ghost components, no by-name bindings
         NOTE: this should never be a singleton list (but it could be empty) *)
      | Tuple of expr_t list

      (* unary expressions: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-unary-expression *)
      | Unary of uop_t * expr_t
      (* NOTE: the following are unsupported
         - as/is: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-as-is-expression
         - bitvector: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-bitvector-expression
      *)
      | Binary of bop_t * expr_t * expr_t
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
         - Call variant: expression must end with a (possibly empty) argument list,
           and might be trailed by attributes
      *)
      | SCall of expr_t * expr_t list * attribute_t list
      (* - Update variant: assignments 1-1, 1-many, many-1, many-many
           NOTE: no havoc or such-that assignments *)
      | SUpdAssign of lhs_t NonEmptyList.t * rhs_t NonEmptyList.t

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
      | ArgList  of expr_t list
    [@@deriving show, eq]

    and member_binding_upd_t = (id_t, int) Either.t * expr_t

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
    and case_expr_t = Case of attribute_t list * extended_pattern_t * expr_t

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
      | DeclIds of var_decl_id_lhs_t list * var_decl_ids_rhs_t

    and var_decl_id_lhs_t = { id: id_t; tp: Type.t option; attrs: attribute_t list }

    (* NOTE: no update-failure, such-that *)
    and var_decl_ids_rhs_t =
      | Assign of rhs_t list

    (** should only be called with relational operators that support chaining,
        and can be chained together *)
    let rec chain_bop (e1: expr_t) (es: (bop_t * expr_t) list): expr_t =
      match es with
      | [] -> e1
      | [(o, e2)] -> Binary (o, e1, e2)
      | (o, e2) :: es ->
        let res = chain_bop e2 es in
        Binary (And, Binary (o, e1, e2), res)

    let assoc_right_bop (o: bop_t) (es: expr_t NonEmptyList.t): expr_t =
      NonEmptyList.fold_right_1 (fun x y -> Binary (o, x, y)) es

    (* let assoc_left_bop (o: bop_t) (es: t NonEmptyList.t): t = *)
    (*   NonEmptyList.fold_left_1 (fun x y ) *)

    let foldl1 (f: expr_t -> expr_t -> expr_t) (es: expr_t list): expr_t =
      match es with
      | [] -> assert false      (* TODO: better error handling (integrate with parser (option)) *)
      | init :: es ->
        List.fold_left f init es
  end

  type module_qualified_name_t = id_t NonEmptyList.t
  [@@deriving show, eq]

  module ModuleItem = struct
    (** Imports  *)
    type module_reference_t = Concrete | Abstract
    [@@deriving show, eq]

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-importing-modules
       NOTE: no export sets *)
    type import_t =
      { opened: bool
      ; mref: (module_reference_t * id_t) option
      ; tgt: module_qualified_name_t
      }
    [@@deriving show, eq]

    type formal_t = Formal of id_t * Type.t
    [@@deriving show, eq]

    type datatype_ctor_t = DatatypeCtor of id_t * formal_t list
    [@@deriving show, eq]

    type function_spec_t =
      | Requires    of Prog.expr_t
      | Reads       of Prog.expr_t
      | Ensures     of Prog.expr_t
      | Decreases   of Prog.expr_t
    [@@deriving show, eq]

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-method-declaration
       NOTE: see MethodKeyword_
       NOTE: Dafny 4 obsolesced "function method", but we are targetting
             Dafny 3
       TODO: support for constructor, twostate lemma, least/greatest
             lemma *)
    type method_decl_t = Method | Lemma
    [@@deriving eq, show]

    type t =
      (* NOTE: no export sets *)
      | Import        of import_t
      | DatatypeDef   of id_t * datatype_ctor_t list
      | Predicate     of id_t * formal_t list * function_spec_t list * Prog.expr_t
      | Function      of id_t * formal_t list * Type.t * function_spec_t list * Prog.expr_t
      | FuncMethod    of id_t * formal_t list * Type.t * function_spec_t list * Prog.expr_t
      (* lemma, method *)
      | Method        of method_decl_t *
                         id_t * formal_t list * formal_t list * function_spec_t list * Prog.stmt_t list
      (* | Lemma         of id * formal list * ctst list * stmt list *)
      | Alias         of id_t * Type.t
    [@@deriving show, eq]
  end

  module FileLevel = struct
    type t =
      | Include of id_t
      | Module  of id_t * ModuleItem.t list
    [@@deriving show, eq]
  end
end

module ParserPass = AST (TrivMetaData)
