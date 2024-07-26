open Internal
open Syntax

module Resolver (M: Syntax.MetaData) = struct
  module AST = Syntax.AST (M)

  let find_topdecl_module_annotation (id: id_t) (anns: Annotation.toplevel_t)
    : (Annotation.module_t, string) Result.t =
    let scrut =
      List.filter
        (function
          | Annotation.Module (m, _) -> m = id
          | _ -> false)
        anns
    in
    match scrut with
    | [] -> Result.Error ("module not found: " ^ id)
    | (Module m_ann :: []) -> Result.Ok m_ann
    | _ -> Result.Error ("module name is ambiguous: " ^ id)

  let find_topdecl_predicate_annotation
      (id: id_t) (anns: Annotation.toplevel_t)
    : (Annotation.predicate_t, string) Result.t =
    let scrut =
      List.filter
        (function
          | Annotation.Predicate (p_id, _) -> p_id = id
          | _ -> false)
        anns
    in
    match scrut with
    | [] -> Result.Error ("predicate not found: " ^ id)
    | (Predicate p_ann :: []) -> Result.Ok p_ann
    | _ -> Result.Error ("predicate name is ambiguous: " ^ id)

end

module ParserPass = Resolver (TrivMetaData)
