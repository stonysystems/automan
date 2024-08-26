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
         "NameResolution.TopLevel.maybe_find_module: name is ambiguous: "
         ^ NonEmptyList.(show pp_id_t qm_id))
      (aux qm_id anns)

  let find_module
      (id: id_t NonEmptyList.t) (anns: Annotation.toplevel_t)
    : (Annotation.module_t, string) Result.t =
    let< opt_m = maybe_find_module id anns in
    Option.fold
      ~none:(Result.Error
               ("TopLevel.find_module: not found: " ^ (NonEmptyList.show pp_id_t id)))
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
      ~none:(Result.Error ("TopLevel.find_predicate: not found: " ^ NonEmptyList.(show pp_id_t id)))
      ~some:Result.ok
      opt_p

  (* TODO: This does not resolve ambiguity in the target type, e.g., multiple
     aliases for type `MyType` distinguished by module qualifications (where we
     should choose the alias for the name that Dafny resolves). We would need to
     follow #include directives and parse the whole Dafny project for that. *)
  let rec maybe_find_tp_alias
    (tp: ParserPass.Type.t) (anns: Annotation.toplevel_t)
    : (Syntax.Common.module_qualified_name_t option, string) Result.t =
    (* 1. Look for type aliases at the current level whose target matches `tp` *)
    let aliases_here = Annotation.filter_by_tp_alias_tgt tp anns in
    match aliases_here with
    | (TypeAlias (id, _) :: []) ->
      Result.Ok (Some (NonEmptyList.singleton id))
    | [] ->
      (* 2. Search modules in scope for target matching `tp`, and add qualifications *)
      (* 2.1. Pick out the module annotations *)
      let m_anns =
        List.filter_map
          (function
            | Annotation.Module m_ann -> Some m_ann
            | _ -> None)
          anns
      in
      (* 2.2 Recursively search each for a type alias annotation *)
      List.foldM_left_result begin fun acc ann ->
          let (id, m_anns) = ann in
          let< r = maybe_find_tp_alias tp m_anns in
          match (acc, r) with
          (* 2.2.1. We haven't found it now or earlier *)
          | (None, None) ->
            Result.Ok None
          (* 2.2.2. Ambiguous type alias *)
          | (Some _, Some _) ->
            Result.Error
              ("NameResolution.TopLevel.maybe_find_tp_alias: multiple (qualilfied) aliases for type:\n"
               ^ ParserPass.Type.(show tp))
          (* 2.2.3. We found it before *)
          | (Some acc', _) ->
            Result.Ok (Some acc')
          (* 2.2.4. We found it now, so qualify with that module id *)
          | (_, Some ids) ->
            Result.Ok (Some (NonEmptyList.cons id ids))
          end
          (Result.Ok None) m_anns
    | _ ->
      Result.Error
        ("NameResolution.TopLevel.maybe_find_tp_alias: multiple toplevel aliases for type:\n"
         ^ ParserPass.Type.(show tp))
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

  let rec maybe_find_module (ns: t) (m_id: module_qualified_name_t)
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
        maybe_find_module ns.enclosing m_id

  (** Searches only the the local namespace for the predicate `m_id` *)
  let maybe_find_predicate_local_decl (ns: t) (m_id: id_t)
    : (Annotation.predicate_t option, string) Result.t =
    match ns with
    | TopLevel ->
      Result.Error
        "NameSpace.find_predicate_local: no local definitions at toplevel"
    | Module ns' ->
      TopLevel.maybe_find_predicate (NonEmptyList.singleton m_id) ns'.locals

  let rec maybe_find_predicate (ns: t) (qm_id: id_t NonEmptyList.t)
      : (Annotation.predicate_t option, string) Result.t =
    match ns with
    | TopLevel ->
      Result.Ok None
    | Module ns' ->
      let< p_local = TopLevel.maybe_find_predicate qm_id ns'.locals in
      match p_local with
      | Some _ -> Result.Ok p_local
      | None ->
        let< p_import = TopLevel.maybe_find_predicate qm_id ns'.imports in
        match p_import with
        | Some _ -> Result.Ok p_import
        | None ->
          maybe_find_predicate ns'.enclosing qm_id

  (* TODO: This does not resolve ambiguity in the target type, e.g., multiple
     definitions of type `MyType` distinguished by module qualifications. We
     would need to follow #include directives and parse the whole Dafny
     project for that.

     TODO: Consider an alias, to be declared in the translation of the current
     module, for a datatype (also declared in this module) that appears after
     some predicates in which the target of the alias appears. *)
  let maybe_find_tp_alias_local_decl (ns: t) (tp: ParserPass.Type.t)
    : (id_t option, string) Result.t =
    match ns with
    | TopLevel ->
      Result.Error
        ("NameResolution.NameSpace.maybe_find_tp_alias_local_decl: no local decls at the toplevel!\n"
         ^ ParserPass.Type.(show tp))
    | Module ns' ->
      let< t_alias = TopLevel.maybe_find_tp_alias tp ns'.locals in
      let ensure_is_local
        : Syntax.Common.module_qualified_name_t -> id_t option =
        function q_id ->
          let (qs, id) = NonEmptyList.unsnoc q_id in
          if List.length qs = 0 then Some id else None
      in
      Result.Ok (Option.fold ~none:None ~some:ensure_is_local t_alias)

  let rec maybe_find_tp_alias (ns: t) (tp: ParserPass.Type.t)
      : (Syntax.Common.module_qualified_name_t option, string) Result.t =
    match ns with
    | TopLevel -> Result.Ok None
    | Module ns' ->
      (* NOTE: Prefer local definitions *)
      let< a_local = TopLevel.maybe_find_tp_alias tp ns'.locals in
      if Option.is_some a_local then Result.Ok a_local else begin
        let< a_import = TopLevel.maybe_find_tp_alias tp ns'.imports in
        if Option.is_some a_import then Result.Ok a_import else
          maybe_find_tp_alias ns'.enclosing tp
      end
end

module Resolver = struct
  open Syntax.Common

  type 'a m = (NameSpace.t, string, 'a) StateError.t

  open struct
    let ( let< )  = Result.bind
    let ( let<* ) = StateError.bind
  end

  let maybe_find_module
      (m_id: module_qualified_name_t) (anns: Annotation.toplevel_t)
    : Annotation.module_t option m =
    StateError.map_error ((^) "Resolver.maybe_find_module:\n") begin
      State.gets begin fun ns ->
        let< m_ann = NameSpace.maybe_find_module ns m_id in
        match m_ann with
        | Some x -> Result.Ok (Some x)
        | None -> TopLevel.maybe_find_module m_id anns
      end
    end

  let find_module
      (m_id: module_qualified_name_t) (anns: Annotation.toplevel_t)
    : Annotation.module_t m =
    let<* m_ann =
      StateError.map_error ((^) "Resolver.find_module:\n")
        (maybe_find_module m_id anns)
    in
    match m_ann with
    | None ->
      StateError.error
        ("Resolver.find_module: not found: "
         ^ NonEmptyList.(show pp_id_t m_id))
    | Some m_ann ->
      StateError.return m_ann

  let maybe_find_predicate_local_decl (m_id: id_t)
    : (Annotation.predicate_t option) m =
    StateError.gets (fun ns -> NameSpace.maybe_find_predicate_local_decl ns m_id)

  let maybe_find_predicate
      (qp_id: id_t NonEmptyList.t) (anns: Annotation.toplevel_t)
    : Annotation.predicate_t option m =
    let<* p_ann =
      StateError.gets (fun ns -> NameSpace.maybe_find_predicate ns qp_id) in
    match p_ann with
    | Some _ -> StateError.return p_ann
    | None ->
      State.return (TopLevel.maybe_find_predicate qp_id anns)

  let maybe_find_tp_alias (tp: ParserPass.Type.t)
    : (Syntax.Common.module_qualified_name_t option) m =
    StateError.gets (fun ns -> NameSpace.maybe_find_tp_alias ns tp)

  let maybe_find_tp_alias_local_decl (tp: ParserPass.Type.t)
    : (id_t option) m =
    StateError.map_error
      ((^) "NameResolution.Resolver.maybe_find_tp_alias_local_decl:\n")
      begin
        StateError.gets (fun ns ->
            NameSpace.maybe_find_tp_alias_local_decl ns tp)
      end

  (** Returns `true` if the import is found, `false` otherwise *)
  let push_import
      (imp: Syntax.Common.import_t) (anns: Annotation.toplevel_t)
    : bool m =
    StateError.map_error ((^) "Resolver.push_import:\n") begin
      let<* m_ann = maybe_find_module imp.tgt anns in
      match m_ann with
      | None ->
        StateError.return false
      | Some (m_id, m_anns) ->
        let imps1 = (if imp.opened then m_anns else []) in
        let imps2 = (match imp.mref with
          | None -> [Annotation.Module (m_id, m_anns)]
          | Some (_, m_ref) -> [Annotation.Module (m_ref, m_anns)])
        in
        let<* () =
          StateError.puts (fun ns ->
              NameSpace.push_imports ns (imps1 @ imps2))
        in
        StateError.return true
    end

  let enter_module (m_id: id_t) (anns: Annotation.toplevel_t)
    : unit m =
    StateError.puts begin fun ns ->
      let qm_id = NameSpace.qualify_module m_id ns in
      let< (_, m_anns) = TopLevel.find_module qm_id anns in
      let ns1 = NameSpace.enter_module ns m_id in
      NameSpace.push_locals ns1 m_anns
    end

  let exit_module: unit m =
    StateError.puts begin fun ns ->
      NameSpace.exit_module ns
    end

  let within_module
      (m_id: id_t) (anns: Annotation.toplevel_t) (p: 'a m)
    : 'a m =
    let<* () = enter_module m_id anns in
    let<* ret = p in
    let<* () = exit_module in
    StateError.return ret

end

