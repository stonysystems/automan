open Internal
open Syntax

module TopLevel = struct
  open struct
    let ( let< ) = Result.( let< )
  end

  let maybe_find_module
      (qm_id: id_t NonEmptyList.t) (anns: Annotation.toplevel_t)
    : (Annotation.module_t option, string) Result.t =
    (* This does the real work; its defined as an auxiliary for error
       reporting *)
    let rec aux qm_id anns =
      let NonEmptyList.( :: ) (qm_id_hd, qm_id_tl) = qm_id in
      match Annotation.filter_by_module_id qm_id_hd anns with
      | [] -> Result.Ok None
      | (Module ((_, m_decls) as m_ann) :: []) ->
        begin
          match qm_id_tl with
          | [] -> Result.Ok (Some m_ann)
          | _ :: _ ->
            aux (NonEmptyList.coerce qm_id_tl) m_decls
        end
      | _ ->
        Result.Error ()
    in
    Result.map_error
      (fun _ ->
         "module name is ambiguous: "
         ^ NonEmptyList.(show pp_id_t qm_id))
      (aux qm_id anns)

  let find_module
      (id: id_t NonEmptyList.t) (anns: Annotation.toplevel_t)
    : (Annotation.module_t, string) Result.t =
    let< opt_m = maybe_find_module id anns in
    Option.fold
      ~none:(Result.Error
               ("module not found: " ^ (NonEmptyList.show pp_id_t id)))
      ~some:Result.ok
      opt_m

  let maybe_find_predicate
      (qp_id: id_t NonEmptyList.t) (anns: Annotation.toplevel_t)
    : (Annotation.predicate_t option, string) Result.t =
    let (qm_id, p_id) = NonEmptyList.unsnoc qp_id in
    let< anns' = begin
      match qm_id with
      | [] ->
        Result.Ok (Some ("", anns))
      | _ :: _ ->
        maybe_find_module (NonEmptyList.coerce qm_id) anns
    end in
    match anns' with
    | None -> Result.Ok None
    | Some (_, m_anns) ->
      match Annotation.filter_by_predicate_id p_id m_anns with
      | [] -> Result.Ok None
      | (Predicate p_ann :: []) ->
        Result.Ok (Some p_ann)
      | _ ->
        Result.Error
          ("predicate name is ambiguous: "
           ^ NonEmptyList.show pp_id_t qp_id)

  let find_predicate
      (id: id_t NonEmptyList.t) (anns: Annotation.toplevel_t)
    : (Annotation.predicate_t, string) Result.t =
    let< opt_p = maybe_find_predicate id anns in
    Option.fold
      ~none:(Result.Error ("module not found: " ^ NonEmptyList.(show pp_id_t id)))
      ~some:Result.ok
      opt_p
end

module NameSpace = struct
  open Common
  open struct
    let ( let< ) = Result.( let< )
  end
  (* NOTE: we assume no toplevel imports or opens (Dafny permits this)
     If we wanted to support this, we would need to process includes as well
  *)
  type t =
    | TopLevel
    | Module of module_t
  [@@deriving show, eq]

  and module_t =
    { enclosing: t
    ; m_id: id_t
    ; imports: Annotation.toplevel_t
    ; locals: Annotation.toplevel_t
    }

  (* [enter|exit]_module are for name resolution during mode analysis *)
  let enter_module (ns: t) (m_id: id_t): module_t =
    { enclosing = ns; m_id = m_id; imports = []; locals = [] }

  let exit_module (ns: module_t): t =
    match ns.enclosing with
    | TopLevel -> TopLevel
    | Module ns' ->
      Module
        { ns' with
          locals =
            ns'.locals @ [Annotation.Module (ns.m_id, ns.locals)]
        }

  let push_imports (ns: module_t) (imps: Annotation.toplevel_t): module_t =
    (* The resolver performs the necessary transformations, e.g., unpacking an
       opened import or renaming on an import alias *)
    { ns with imports = imps @ ns.imports }

  let find_module_local (ns: module_t) (m_id: module_qualified_name_t) =
    (* Search local declarations first, then search local imports *)
    let< tmp = TopLevel.maybe_find_module m_id ns.locals in
    match tmp with
    | Some _ -> Result.Ok tmp
    | None ->
      TopLevel.maybe_find_module m_id ns.imports

  let rec find_module (ns: t) (m_id: module_qualified_name_t)
    : (Annotation.module_t option, string) Result.t =
    match ns with
    | TopLevel ->
      (* We reached the toplevel and found nothing; the resolver will search the
         toplevel if appropriate *)
      Result.Ok None
    | Module ns ->
      (* Try to find the module locally (in decls and imports) first; otherwise,
         search the enclosing module *)
      let< opt_m_ann = find_module_local ns m_id in
      if Option.is_some opt_m_ann then
        Result.Ok opt_m_ann
      else
        find_module ns.enclosing m_id
end

module Resolver (M: Syntax.MetaData) = struct
  module AST = Syntax.AST (M)

  (* open struct *)
  (*   let ( let+ ) = Option.bind *)
  (* end *)

  (* (\** *)
  (*  * - qpid: the (possibly qualified) name of the predicate to search for *)
  (*  * - anns: the annotations to search *)
  (*  * - m_id: id of the module within which the predicate is invoked *)
  (*  * - imports: the import directives preceding the invoked predicate *)
  (* *\) *)
  (* let rec find_qualified_predicate_annotation *)
  (*     (qp_id: Syntax.Common.module_qualified_name_t) *)
  (*     (anns: Annotation.toplevel_t) *)
  (*     (m_id: id_t list) *)
  (*     (imports: Syntax.Common.import_t list) *)
  (*   : Annotation.predicate_t option = *)
  (*   match anns with *)
  (*   | [] -> None *)
  (*   | Predicate (p'_id, p'_modes) :: anns -> *)
  (*     let qp'_id = NonEmptyList.(p'_id :: []) in *)
  (*     if (NonEmptyList.(equal ( = ) qp'_id qp_id)) then *)
  (*       Option.Some (p'_id, p'_modes) *)
  (*     else *)
  (*       find_qualified_predicate_annotation qp_id anns m_id imports *)
  (*   | Module (m'_id, m'_anns) :: anns -> *)
  (*     (\* For qp_id to be defined in m'_ann, one of the following must hold *)
  (*     - m'_id = head m_id,  and qp_id is in m'_anns (with tail m_id) *)
  (*     - m'_id = head qp_id, and tail qp_id is in  *)
  (*     *\) *)
  (*     foo2 *)

end

module ParserPass = Resolver (TrivMetaData)
