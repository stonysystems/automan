open Core
open Lexing
(* open Internal *)
open Internal.NonEmptyList
open TestCommon

module TypeTableBuilder = struct
  type module_table_t = {
    decls : (string, Syntax.ParserPass.TopDecl.t) Hashtbl.t;
    imports : Syntax.ParserPass.TopDecl.t list ref;
  }

  type t = {
    decls_table : (string, module_table_t) Hashtbl.t;
    mutable processed_files : (string, bool) Hashtbl.t;
  }

  let create () = {
    decls_table = Hashtbl.create (module String);
    processed_files = Hashtbl.create (module String);
  }

  let file_exists path =
    match Sys_unix.file_exists path with
    | `Yes -> true
    | `No | `Unknown -> false
    
  let add_decl_to_module builder_instance module_name decl =
    let module_table =
      Hashtbl.find_or_add builder_instance.decls_table module_name
        ~default:(fun () -> {
          decls = Hashtbl.create (module String);
          imports = ref [];
        })
    in
    match snd decl with
    | Syntax.ParserPass.TopDecl.DatatypeDecl ((), _, id, _, _)
    | Syntax.ParserPass.TopDecl.SynonymTypeDecl {id; _} ->
        Hashtbl.set module_table.decls ~key:id ~data:decl
    | Syntax.ParserPass.TopDecl.ModuleImport _ ->
        module_table.imports := decl :: !(module_table.imports)
    | _ -> ()

  let rec filter_datatype_synonym_and_imports decls module_name builder_instance =
    List.iter decls ~f:(fun decl ->
      match snd decl with
      | Syntax.ParserPass.TopDecl.DatatypeDecl _
      | Syntax.ParserPass.TopDecl.SynonymTypeDecl _
      | Syntax.ParserPass.TopDecl.ModuleImport _ ->
          add_decl_to_module builder_instance module_name decl
      | Syntax.ParserPass.TopDecl.ModuleDef (_, id, inner_decls) ->
          filter_datatype_synonym_and_imports inner_decls id builder_instance
      | _ -> ()
    )

  let parse_and_filter filename builder_instance =
    if Hashtbl.mem builder_instance.processed_files filename then
      ([], [])
    else begin
      Hashtbl.add_exn builder_instance.processed_files ~key:filename ~data:true;
      let inx = In_channel.create filename in
      let lexbuf = Lexing.from_channel inx in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      let result = parse_dafny_return_error lexbuf in
      In_channel.close inx;
      match result with
      | Result.Ok ast -> 
        (match ast with
          | Syntax.ParserPass.Dafny { decls; includes } ->
            filter_datatype_synonym_and_imports decls "global" builder_instance;
              (decls, includes))
      | Result.Error msg -> 
        printf "Error while parsing file: %s\n%s" filename msg;
        ([], [])
    end

  let rec parse_includes current_file includes builder_instance =
    let current_dir = Filename.dirname current_file in
    List.concat_map includes ~f:(fun include_file ->
      let include_path = Filename.concat current_dir include_file in
      if Hashtbl.mem builder_instance.processed_files include_path then
        []
      else begin
        if file_exists include_path then begin
          printf "Parsing include file: %s\n" include_path;
          let (filtered_decls, inner_includes) = parse_and_filter include_path builder_instance in
          filtered_decls @ parse_includes include_path inner_includes builder_instance
        end else begin
          printf "Warning: Include file not found: %s\n" include_path;
          []
        end
      end
    )

  let build_type_table filename builder_instance =
    let (filtered_decls, includes) = parse_and_filter filename builder_instance in
    let include_decls = parse_includes filename includes builder_instance in
    filtered_decls @ include_decls

  (* find type decl by both moudle name and type name *)
  let find_type_decl_by_module_and_type_name builder_instance module_name type_name =
    match Hashtbl.find builder_instance.decls_table module_name with
    | Some module_table -> 
      (match Hashtbl.find module_table.decls type_name with
      | Some decl -> Some (module_name, decl)
      | None -> None)
    | None -> None
    
  
  
  (* find type decl by only the type name *)
  (* if multiple types have the same name, it will return a list, contains all type decls and the moudles they belong to *)
  let find_all_type_decls_by_type_name builder_instance type_name =
    let results = ref [] in
    Hashtbl.iteri builder_instance.decls_table ~f:(fun ~key:module_name ~data:module_table ->
      match Hashtbl.find module_table.decls type_name with
      | Some decl -> results := (module_name, decl) :: !results
      | None -> ()
    );
    !results
  
  (* find the import list of a module *)
  let find_module_imports builder_instance module_name =
    match Hashtbl.find builder_instance.decls_table module_name with
    | Some module_table -> !(module_table.imports)
    | None -> []
  
  let get_target_name tgt =
    match as_list tgt with
    | [head] -> head
    | _ -> List.last_exn (as_list tgt)
    

  (* find decl by only type name. 
     when multiple types with the same name, using imports to find the correct one *)
  let find_type_decl_by_type_name_with_imports builder_instance type_name module_name =
    let decls = find_all_type_decls_by_type_name builder_instance type_name in

    match Hashtbl.find builder_instance.decls_table module_name with
    | Some module_table ->
      let open_imports = List.filter !(module_table.imports) ~f:(function
        | _, Syntax.ParserPass.TopDecl.ModuleImport { opened = true; _ } -> true
        | _ -> false)
      in

      let results = List.filter decls ~f:(fun (decl_module_name, _) ->
        List.exists open_imports ~f:(function
          | _, Syntax.ParserPass.TopDecl.ModuleImport { tgt; _ } ->
            let import_module_name = 
              get_target_name tgt
            in
            String.equal import_module_name decl_module_name
          | _ -> false
        )
      )
      in
      results
    | None ->
      []

  (* find decl by both module name and type name *)
  (* before searching, first determine if the moudle name is a alias *)
  let find_type_decl_by_module_and_type_name_with_imports builder_instance type_name module_name using_module =
    match Hashtbl.find builder_instance.decls_table using_module with
    | Some module_table ->
        let imports = !(module_table.imports) in
        let resolved_module_name = 
          List.fold_left imports ~init:module_name ~f:(fun acc import_decl ->
            match import_decl with
            | _, Syntax.ParserPass.TopDecl.ModuleImport { tgt; mref = Some (_, alias); _ }
              when String.equal alias module_name ->
                get_target_name tgt
            | _ -> acc
          )
        in
        
        find_type_decl_by_module_and_type_name builder_instance resolved_module_name type_name
        
    | None -> None
      

end
