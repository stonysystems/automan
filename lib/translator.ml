(** Final translation phase *)

open Syntax
open Internal

module Definitions = struct
  type predicate_decl_t =
    | Predicate
    | Function of
        { in_vars:  ParserPass.TopDecl.formal_t list
        ; out_vars: ParserPass.TopDecl.formal_t NonEmptyList.t
        ; requires: ParserPass.Prog.expr_t list }
  [@@deriving show, eq]

  type ite_functionalize_t =
    { assigned_vars: Common.member_qualified_name_t NonEmptyList.t
    ; then_permutation: Common.member_qualified_name_t NonEmptyList.t
    ; else_permutation: Common.member_qualified_name_t NonEmptyList.t }
  [@@deriving show, eq]

  type match_functionalize_t =
    { assigned_vars: Common.member_qualified_name_t NonEmptyList.t
    ; permutations:  (Common.member_qualified_name_t NonEmptyList.t) NonEmptyList.t
    }
  [@@deriving show, eq]

  type quantification_forall_functionalize_collection_t =
    | QFSeq of ParserPass.Prog.seq_display_t
    | QFMap of ParserPass.Prog.map_comp_t
    | QFSet of ParserPass.Prog.set_comp_t
  [@@deriving show, eq]

  type quantification_forall_functionalize_t =
    { out_var: Common.member_qualified_name_t
    ; collection: quantification_forall_functionalize_collection_t
    }
  [@@deriving show, eq]

  type unary_op_for_outvar_t = Cardinality
  [@@deriving show, eq]

  type binary_op_eq_functionalize_t =
    { outvar_is_left: bool
    ; outvar: Common.member_qualified_name_t
    ; outvar_op: unary_op_for_outvar_t option
    }
  [@@deriving show, eq]

  type arglist_functionalize_t =
    { callee: id_t NonEmptyList.t
    ; input: ParserPass.Prog.expr_t list
    ; output: Common.member_qualified_name_t NonEmptyList.t
    }
  [@@deriving show, eq]
end

module TranslationMetaData : MetaData
  with type predicate_decl_t = Definitions.predicate_decl_t

  with type ite_t     = Definitions.ite_functionalize_t option
  with type match_t   = Definitions.match_functionalize_t option
  with type quantification_t =
         Definitions.quantification_forall_functionalize_collection_t option
  with type binary_op_t = Definitions.binary_op_eq_functionalize_t option

  with type arglist_t = Definitions.arglist_functionalize_t option
= struct
  type predicate_decl_t = Definitions.predicate_decl_t
  [@@deriving show, eq]

  type datatype_decl_t = Annotator.AnnotationMetaData.datatype_decl_t
  [@@deriving show, eq]

  type synonym_type_decl_t = Annotator.AnnotationMetaData.synonym_type_decl_t
  [@@deriving show, eq]

  type type_t = Annotator.AnnotationMetaData.type_t
  [@@deriving show, eq]

  type ite_t     = Definitions.ite_functionalize_t option
  [@@deriving show, eq]

  type match_t   = Definitions.match_functionalize_t option
  [@@deriving show, eq]

  type quantification_t =
    Definitions.quantification_forall_functionalize_collection_t option
  [@@deriving show, eq]

  type binary_op_t = Definitions.binary_op_eq_functionalize_t option
  [@@deriving show, eq]

  type arglist_t = Definitions.arglist_functionalize_t option
  [@@deriving show, eq]
end
