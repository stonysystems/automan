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

type id   = string
[@@deriving show, eq]

(* https://dafny.org/dafny/DafnyRef/DafnyRef.html#172753-basic-name-and-type-combinations *)
type dotsuffix =
  | DSRequires | DSReads
  | DSId  of id
  | DSDig of int (* NOTE: natural number*)
[@@deriving show, eq]

module AST (M : MetaData) = struct

  (** Types
      https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-types
  *)
  module Type = struct
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-type *)
    type name_seg = TpIdSeg of {id: id; gen_inst: t list }
    [@@deriving show, eq]

    (* NOTE: no function types *)
    and t =
      | TpName of name_seg NonEmptyList.t
      (* NOTE: this representation allows singleton tuples *)
      | TpTup  of t list
    [@@deriving show, eq]

    let simple_generic (id: id) (gen_inst: t list) =
      TpName (NonEmptyList.singleton
                (TpIdSeg {id = id; gen_inst = gen_inst}))

    let simple (id: id): t = simple_generic id []

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
  type augmented_dotsuffix = dotsuffix * Type.t list
  [@@deriving show, eq]

  (** Expressions
      https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-expressions
  *)
  module Expr = struct
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
    type name_seg = id * Type.t list
    [@@deriving show, eq]

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-case-pattern
       TODO: possibly *negated* literal expression
       NOTE: if we support disjunctive patterns, rename to
       "single_extended_pattern" *)
    type extended_pattern =
      | EPatLit  of lit_t
      | EPatVar  of id * Type.t option
      (* NOTE: PatCtor (None, pats) means a tuple *)
      (* TODO: can the constructor identifier be qualified? *)
      | EPatCtor of id option * extended_pattern list
    [@@deriving eq, show]

    type pattern =
      | PatVar  of id * Type.t option
      | PatCtor of id option * pattern list
    [@@deriving eq, show]

    type t =
      (* primary expressions:
         https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-primary-expression *)
      | Suffixed of t * suffix
      (*  - name segment expressions **)
      | NameSeg of name_seg

      (* - lambda expressions
           https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-lambda-expression
           TODO: lambda_spec? *)
      | Lambda  of (id * Type.t option) list * t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-map-display-expression
         NOTE: no imap *)
      | MapDisplay of (t * t) list
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-seq-comprehension *)
      | SeqDisplay of seq_display
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-set-display-expression
         NOTE: no multiset, multiset from sequence *)
      | SetDisplay of t list

      (* primary: endless
         https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-endless-expression *)
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-if-expression
         NOTE: no binding guards*)
      | If of t * t * t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-match-expression *)
      | Match of t * case_expr list
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-quantifier-expression
         NOTE: Dafny 3 does not support per-variable quantifier ranges, so we
         aren't either *)
      | Quantifier of
          { qt : quantifier_t
          ; qdom : qdom
          ; qbody : t }
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-set-comprehension-expression
         NOTE: no support for iset
         NOTE: no per-variable quantifier ranges *)
      | SetComp of qdom * t option
      (* TODO: StmtInExpr https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-statement-in-an-expression
         This would require making expr and stmt mutually recursive *)
    (* | ... *)
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-let-expression
         NOTE: no let-fail, assign-such-that *)
      | Let of
          { ghost: bool
          ; pats: pattern NonEmptyList.t
          ; def: t NonEmptyList.t
          ; body: t}
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-map-comprehension-expression
         NOTE: imap not supported *)
      | MapComp of { qdom: qdom; key: t option; valu: t }
    (* const atom expressions: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-atomic-expression
       NOTE: no fresh, allocated, unchanged, old *)
      | Lit  of lit_t
      | This
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-cardinality-expression
         NOTE: previously ExprLen *)
      | Cardinality of t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-parenthesized-expression
         NOTE: no ghost components, no by-name bindings
         NOTE: this should never be a singleton list (but it could be empty) *)
      | Tuple of t list

    (* unary expressions: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-unary-expression *)
      | Unary of uop_t * t
    (* NOTE: the following are unsupported
       - as/is: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-as-is-expression
       - bitvector: https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-bitvector-expression
    *)
      | Binary of bop_t * t * t
    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-top-level-expression *)
      | Lemma of {lem: t; e: t}
    [@@deriving show, eq]

    (** Suffixes
        https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-suffix
    *)
    and suffix =
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-augmented-dot-suffix *)
      | AugDot   of augmented_dotsuffix
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-datatype-update-suffix *)
      | DataUpd  of member_binding_upd NonEmptyList.t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-subsequence-suffix *)
      | Subseq   of {lb: t option; ub: t option}
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-subsequence-slices-suffix *)
      | SliceLen of {sublens: t NonEmptyList.t; to_end: bool }
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-sequence-update-suffix
         NOTE: The grammar says there's only one update, but the example shows
         multiple *)
      | SeqUpd   of {idx: t; v: t}
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-selection-suffix
         NOTE: multiple indices (for multi-dimensional arrays) not (yet?) supported *)
      | Sel      of t
      (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-argument-list-suffix *)
      | ArgList  of t list
    [@@deriving show, eq]

    and member_binding_upd = (id, int) Either.t * t

    and seq_display =
      | SeqEnumerate of t list
      | SeqTabulate  of
          { gen_inst: Type.t list
          ; len: t
          ; func: t
          }

    and attribute = string * t list

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-case-pattern
       NOTE: disjunctive patterns unsupported *)
    and case_expr = Case of attribute list * extended_pattern * t

    (* https://dafny.org/dafny/DafnyRef/DafnyRef.html#g-quantifier-expression *)
    and qvar_decl =
      QVar of id * Type.t option * t option * attribute list

    and qdom =
      QDom of {qvars: qvar_decl list; qrange: t option}

    (** `should only be called with relational operators that support chaining,
        and can be chained together *)
    let rec chain_bop (e1: t) (es: (bop_t * t) list): t =
      match es with
      | [] -> e1
      | [(o, e2)] -> Binary (o, e1, e2)
      | (o, e2) :: es ->
        let res = chain_bop e2 es in
        Binary (And, Binary (o, e1, e2), res)

    let assoc_right_bop (o: bop_t) (es: t NonEmptyList.t): t =
      NonEmptyList.fold_right_1 (fun x y -> Binary (o, x, y)) es

    (* let assoc_left_bop (o: bop_t) (es: t NonEmptyList.t): t = *)
    (*   NonEmptyList.fold_left_1 (fun x y ) *)

    let foldl1 (f: t -> t -> t) (es: t list): t =
      match es with
      | [] -> assert false      (* TODO: better error handling (integrate with parser (option)) *)
      | init :: es ->
        List.fold_left f init es
  end

  module ModuleItem = struct
    type formal = Formal of id * Type.t
    [@@deriving show, eq]

    type datatype_ctor = DatatypeCtor of id * formal list
    [@@deriving show, eq]

    type function_spec =
      | Requires    of Expr.t
      | Reads       of Expr.t
      | Ensures     of Expr.t
      | Decreases   of Expr.t
    [@@deriving show, eq]

    type t =
      | Import        of id
      | DatatypeDef   of id * datatype_ctor list
      | Predicate     of id * formal list * function_spec list * Expr.t
      | Function      of id * formal list * Type.t * function_spec list * Expr.t
      | FuncMethod    of id * formal list * Type.t * function_spec list * Expr.t
      (* | Method        of id * formal list * return_mthd * ctst list * stmt list *)
      (* | Lemma         of id * formal list * ctst list * stmt list *)
      | Alias         of id * Type.t
    [@@deriving show, eq]
  end

  module FileLevel = struct
    type t =
      | Include of id
      | Module  of id * ModuleItem.t list
    [@@deriving show, eq]
  end
end

module ParserPass = AST (TrivMetaData)
