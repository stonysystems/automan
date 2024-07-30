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

  let qualify_module (m_id: id_t) (ns: t): module_qualified_name_t =
    let rec aux accum = function
      | TopLevel -> accum
      | Module {enclosing = p; m_id = m_id; imports = _; locals = _} ->
        aux (m_id :: accum) p
    in
    NonEmptyList.coerce (aux [] ns @ [m_id])

  (* [enter|exit]_module are for name resolution during mode analysis *)
  let enter_module (ns: t) (m_id: id_t): t =
    Module { enclosing = ns; m_id = m_id; imports = []; locals = [] }

  let exit_module (ns: t): (t, string) Result.t =
    match ns with
    | TopLevel -> Result.Error ("NameSpace.exit_module: at toplevel")
    | Module ns ->
      match ns.enclosing with
      | TopLevel -> Result.Ok TopLevel
      | Module ns' -> Result.Ok begin
        Module
          { ns' with
            locals =
              ns'.locals @ [Annotation.Module (ns.m_id, ns.locals)] }
      end

  let push_imports (ns: t) (imps: Annotation.toplevel_t)
    : (t, string) Result.t =
    (* The resolver performs the necessary transformations, e.g., unpacking an
       opened import or renaming on an import alias *)
    match ns with
    | TopLevel -> Result.Error begin
        "NameSpace.push_import: cannot import at toplevel"
        ^ "\n- import: " ^ Annotation.(show_toplevel_t imps)
      end
    | Module ns -> Result.Ok begin
        Module { ns with imports = ns.imports @ imps }
      end

  let push_locals (ns: t) (locals: Annotation.toplevel_t)
      : (t, string) Result.t =
    match ns with
    | TopLevel -> Result.Error begin
        "NameSpace.push_locals: cannot make local declaration at toplevel"
        ^ "\n- locals: " ^ Annotation.(show_toplevel_t locals)
      end
    | Module ns -> Result.Ok begin
        Module { ns with locals = ns.locals @ locals }
      end

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

  let find_predicate_local_decl (ns: t) (m_id: id_t)
    : (Annotation.predicate_t, string) Result.t =
    match ns with
    | TopLevel ->
      Result.Error
        "NameSpace.find_predicate_local: no local definitions at toplevel"
    | Module ns' ->
      TopLevel.find_predicate (NonEmptyList.singleton m_id) ns'.locals
end

module Resolver = struct
  open Syntax.Common

  type 'a m = (NameSpace.t, string, 'a) StateError.t

  open struct
    let ( let< )  = Result.bind
    let ( let<* ) = StateError.bind
  end

  let find_module
      (m_id: module_qualified_name_t) (anns: Annotation.toplevel_t)
    : Annotation.module_t m =
    State.gets begin fun ns ->
      let< m_ann = NameSpace.find_module ns m_id in
      match m_ann with
      | Some x -> Result.Ok x
      | None -> TopLevel.find_module m_id anns
    end

  let find_predicate_local_decl (m_id: id_t): Annotation.predicate_t m =
    StateError.gets (fun ns -> NameSpace.find_predicate_local_decl ns m_id)

  let push_import
      (imp: Syntax.Common.import_t) (anns: Annotation.toplevel_t)
    : unit m =
    let<* (m_id, m_anns) =
      StateError.map_error ((^) "Resolver.push_import:\n")
        (find_module imp.tgt anns)
    in
    let imps1 = if imp.opened then m_anns else [] in
    let imps2 =
      match imp.mref with
      | None -> [Annotation.Module (m_id, m_anns)]
      | Some (_, m_ref) -> [Annotation.Module (m_ref, m_anns)]
    in
    StateError.map_error ((^) "Resolver.push_import:\b") begin
      StateError.puts (fun ns -> NameSpace.push_imports ns (imps1 @ imps2))
    end

  let enter_module (m_id: id_t) (anns: Annotation.toplevel_t)
    : unit m =
    StateError.puts begin fun ns ->
      let qm_id = NameSpace.qualify_module m_id ns in
      let< (_, m_anns) = TopLevel.find_module qm_id anns in
      let ns1 = NameSpace.enter_module ns m_id in
      NameSpace.push_locals ns1 m_anns
    end
    (* let<* ns = StateError.get in *)
    (* let qm_id = NameSpace.qualify_module m_id ns in *)
    (* foo *)

    (* let<* ns = StateError.get in *)
    (* StateError.put (NameSpace.enter_module ns m_id) *)

  let exit_module: unit m =
    StateError.puts begin fun ns ->
      NameSpace.exit_module ns
    end

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

