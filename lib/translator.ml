(** Final translation phase *)

open Syntax
open Internal

module Definitions = struct

  type ite_functionalize_t =
    { assigned_vars: Moder.Definitions.outvar_lhs_t NonEmptyList.t
    ; branch_permutations: Moder.Definitions.ite_functionalize_t
    }
  [@@deriving show, eq]

  type match_functionalize_t =
    { assigned_vars: Moder.Definitions.outvar_lhs_t NonEmptyList.t
    ; permutations:  Moder.Definitions.match_functionalize_t
    }
  [@@deriving show, eq]

  type quantification_forall_functionalize_collection_t =
    | QFSeq of ParserPass.Prog.seq_display_t
    | QFMap of ParserPass.Prog.map_comp_t
    | QFSet of ParserPass.Prog.set_comp_t
  [@@deriving show, eq]

  type quantification_forall_functionalize_t =
    { out_var: Moder.Definitions.quantification_functionalize_t
    ; collection: quantification_forall_functionalize_collection_t
    }
  [@@deriving show, eq]

  type binary_op_functionalize_t = Moder.Definitions.binary_op_functionalize_t
  [@@deriving show, eq]

  type arglist_functionalize_t = Moder.Definitions.arglist_functionalize_t
  [@@deriving show, eq]
end

module TranslationMetaData : MetaData
  with type predicate_decl_t    = Moder.ModingMetaData.predicate_decl_t
  with type datatype_decl_t     = Annotator.AnnotationMetaData.datatype_decl_t
  with type synonym_type_decl_t = Annotator.AnnotationMetaData.synonym_type_decl_t

  with type type_t = Annotator.AnnotationMetaData.type_t

  with type ite_t     = Definitions.ite_functionalize_t option
  with type match_t   = Definitions.match_functionalize_t option
  with type quantification_t =
         Definitions.quantification_forall_functionalize_collection_t option
  with type binary_op_t = Definitions.binary_op_functionalize_t option

  with type arglist_t = Definitions.arglist_functionalize_t option
= struct
  type predicate_decl_t = Moder.ModingMetaData.predicate_decl_t
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

  type binary_op_t = Definitions.binary_op_functionalize_t option
  [@@deriving show, eq]

  type arglist_t = Definitions.arglist_functionalize_t option
  [@@deriving show, eq]
end
