  open Core
  open Lexing
  (* open Internal *)
  open Internal.NonEmptyList
  open TestCommon

  module TypeTableBuilder = struct
    (* global type table for a file and its includes *)
    type module_table_t = {
      decls : (string, Syntax.ParserPass.TopDecl.t) Hashtbl.t;
      imports : Syntax.ParserPass.TopDecl.t list ref;
      nested : string list ref;
    }

    type t = {
      decls_table : (string, module_table_t) Hashtbl.t;
      mutable processed_files : (string, bool) Hashtbl.t;
    }

    (* the visible type table for a moudle *)
    type visible_decls_t = {
      self_decls : Syntax.ParserPass.TopDecl.t list;
      opened_imports : (string, module_table_t) Hashtbl.t;
      non_opened_imports_or_nested : (string, module_table_t) Hashtbl.t;
    }

    let create () = {
      decls_table = Hashtbl.create (module String);
      processed_files = Hashtbl.create (module String);
    }

    let cached_visible_decls : visible_decls_t option ref = ref None

    let cache_visible_decls new_visible_decls =
      cached_visible_decls := Some new_visible_decls

    let get_cached_visible_decls () =
      !cached_visible_decls
        
    let clear_visible_decls_cache () =
      cached_visible_decls := None

    let file_exists path =
      match Sys_unix.file_exists path with
      | `Yes -> true
      | `No | `Unknown -> false
    
    let rec filter_datatype_synonym_and_imports decls module_name_opt builder_instance =
      let module_name = match module_name_opt with
        | Some name -> name
        | None -> ""
      in
      let add_decl_to_module module_name decl =
        let module_table =
          Hashtbl.find_or_add builder_instance.decls_table module_name
            ~default:(fun () -> {
              decls = Hashtbl.create (module String);
              imports = ref [];
              nested = ref [];
            })
        in
        match snd decl with
        | Syntax.ParserPass.TopDecl.DatatypeDecl ((), _, id, _, _)
        | Syntax.ParserPass.TopDecl.SynonymTypeDecl {id; _} ->
            Hashtbl.set module_table.decls ~key:id ~data:decl
        | Syntax.ParserPass.TopDecl.ModuleDef (_, nested_module_name, inner_decls) ->
            let nested_module_full_name = 
              if String.is_empty module_name then nested_module_name 
              else module_name ^ "." ^ nested_module_name
            in

            let rec add_nested_to_ancestors ancestor_name =
              match Hashtbl.find builder_instance.decls_table ancestor_name with
              | Some ancestor_table ->
                  ancestor_table.nested := nested_module_full_name :: !(ancestor_table.nested);
                  if String.contains ancestor_name '.' then
                    let parent_name = String.rsplit2_exn ancestor_name ~on:'.' |> fst in
                    add_nested_to_ancestors parent_name
              | None -> ()
            in

            add_nested_to_ancestors module_name;
            filter_datatype_synonym_and_imports inner_decls (Some nested_module_full_name) builder_instance
        | Syntax.ParserPass.TopDecl.ModuleImport _ ->
            module_table.imports := decl :: !(module_table.imports)
        | _ -> ()
      in

      List.iter decls ~f:(fun decl ->
        match snd decl with
        | Syntax.ParserPass.TopDecl.DatatypeDecl _ 
        | Syntax.ParserPass.TopDecl.SynonymTypeDecl _ 
        | Syntax.ParserPass.TopDecl.ModuleImport _ 
        | Syntax.ParserPass.TopDecl.ModuleDef _ -> 
            add_decl_to_module module_name decl
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
              filter_datatype_synonym_and_imports decls None builder_instance;
                (decls, includes))
        | Result.Error _msg -> 
          (* printf "Error while parsing file: %s\n%s" filename msg; *)
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
            (* printf "Parsing include file: %s\n" include_path; *)
            let (filtered_decls, inner_includes) = parse_and_filter include_path builder_instance in
            filtered_decls @ parse_includes include_path inner_includes builder_instance
          end else begin
            (* printf "Warning: Include file not found: %s\n" include_path; *)
            []
          end
        end
      )

    (* build the global type table for a file *)
    let build_type_table filename builder_instance =
      let (filtered_decls, includes) = parse_and_filter filename builder_instance in
      let include_decls = parse_includes filename includes builder_instance in
      filtered_decls @ include_decls

    
    (* find the self declarations of a module *)
    let find_self_decls module_table =
      Hashtbl.fold module_table.decls ~init:[] ~f:(fun ~key:_ ~data:decl acc ->
        match snd decl with
        | Syntax.ParserPass.TopDecl.DatatypeDecl _
        | Syntax.ParserPass.TopDecl.SynonymTypeDecl _ -> decl :: acc
        | _ -> acc
      )

    let rec add_nested_modules_to acc nested_module_name builder_instance prefix =
      match Hashtbl.find builder_instance.decls_table nested_module_name with
      | Some nested_table ->
          (* Add the name with the prefix removed to the accumulator *)
          let stripped_nested_name =
            if String.is_prefix nested_module_name ~prefix then
              String.chop_prefix_exn nested_module_name ~prefix  (* Remove the prefix *)
            else
              nested_module_name  (* No prefix, do nothing *)
          in
          Hashtbl.set acc ~key:stripped_nested_name ~data:nested_table;
    
          (* Recursively handle the nested sub-modules *)
          List.iter !(nested_table.nested) ~f:(fun deeper_nested_name ->
            add_nested_modules_to acc deeper_nested_name builder_instance prefix
          )
      | None -> ()
      

    let rec find_in_ancestor_nested ancestor_name nested_name builder_instance =
      if String.is_empty ancestor_name then
        None
      else
        let full_nested_name = ancestor_name ^ "." ^ nested_name in
        match Hashtbl.find builder_instance.decls_table ancestor_name with
        | Some ancestor_table ->
          (* Find matches in the top-level nested modules of the ancestor module *)
          (match List.find !(ancestor_table.nested) ~f:(fun nested_full_name ->
            String.equal nested_full_name full_nested_name
          ) with
          | Some found_nested_name -> Some found_nested_name
          | None ->
            (* Recursively look for higher ancestors *)
            (match String.rsplit2 ancestor_name ~on:'.' with
              | Some (parent_name, _) -> find_in_ancestor_nested parent_name nested_name builder_instance
              | None -> None))
        | None -> None
    ;;


    let find_opened_imports builder_instance current_module_name module_table non_opened_imports_or_nested =
      List.fold !(module_table.imports) ~init:(Hashtbl.create (module String)) ~f:(fun acc import_decl ->
        match snd import_decl with
        | Syntax.ParserPass.TopDecl.ModuleImport { opened = true; tgt; _ } ->
          let import_name = String.concat ~sep:"." (as_list tgt) in
          
          (* Use the concatenated full module name to search in nested *)
          (match find_in_ancestor_nested current_module_name import_name builder_instance with
          | Some nested_full_name ->
              (* Found the nested module, add it to the opened list, but its nested modules go into non-opened *)
              (match Hashtbl.find builder_instance.decls_table nested_full_name with
              | Some nested_table ->
                  Hashtbl.set acc ~key:nested_full_name ~data:nested_table;
                  (* Add all the nested modules of this nested module into non-opened *)
                  List.iter !(nested_table.nested) ~f:(fun deeper_nested_name ->
                    (* Remove the prefix `import_name` and keep only the remaining part *)
                    let trimmed_nested_name =
                      if String.is_prefix deeper_nested_name ~prefix:nested_full_name then
                        String.chop_prefix_exn deeper_nested_name ~prefix:(nested_full_name ^ ".")
                      else
                        deeper_nested_name
                    in
                    (* printf "full name: %s, import name: %s, trimmed_name: %s\n" deeper_nested_name nested_full_name trimmed_nested_name; *)
                    Hashtbl.set non_opened_imports_or_nested ~key:trimmed_nested_name ~data:(Hashtbl.find_exn builder_instance.decls_table deeper_nested_name)
                  );
                  acc
              | None -> acc)
          | None ->
            (* If not found in the ancestor module, search in the global table *)
            (match Hashtbl.find builder_instance.decls_table import_name with
              | Some global_import_table ->
                  (* The module itself should be added to opened_imports *)
                  Hashtbl.set acc ~key:import_name ~data:global_import_table;
                  (* Add the nested modules of the global module into non_opened, remove `import_name` prefix *)
                  List.iter !(global_import_table.nested) ~f:(fun deeper_nested_name ->
                    let trimmed_nested_name =
                      if String.is_prefix deeper_nested_name ~prefix:import_name then
                        String.chop_prefix_exn deeper_nested_name ~prefix:(import_name ^ ".")
                      else
                        deeper_nested_name
                    in
                    Hashtbl.set non_opened_imports_or_nested ~key:trimmed_nested_name ~data:(Hashtbl.find_exn builder_instance.decls_table deeper_nested_name)
                  );
                  acc
              | None -> acc))
        | _ -> acc
      )
    ;;

    let find_non_opened_imports_or_nested builder_instance module_name module_table non_opened_imports_or_nested =
      (* Helper function to add module and its nested to non-opened, while keeping only the last part after the final "." *)
      let add_module_and_nested_to_non_opened module_full_name =
        (* Calculate the prefix to remove *)
        let prefix =
          match String.rsplit2 module_full_name ~on:'.' with
          | Some (prefix, _) -> prefix ^ "."  (* Keep the prefix with "." *)
          | None -> ""  (* No prefix, return empty string *)
        in
        match Hashtbl.find builder_instance.decls_table module_full_name with
        | Some module_table ->
            (* Add the name with the prefix removed to non-opened *)
            let stripped_name =
              if String.is_prefix module_full_name ~prefix then
                String.chop_prefix_exn module_full_name ~prefix  (* Remove the prefix *)
              else
                module_full_name
            in
            Hashtbl.set non_opened_imports_or_nested ~key:stripped_name ~data:module_table;
      
            (* Recursively handle the nested modules, passing the calculated prefix *)
            List.iter !(module_table.nested) ~f:(fun nested_name ->
              add_nested_modules_to non_opened_imports_or_nested nested_name builder_instance prefix
            )
        | None -> ()
      in

      (* Non-opened imports *)
      List.iter !(module_table.imports) ~f:(fun import_decl ->
        match snd import_decl with
        | Syntax.ParserPass.TopDecl.ModuleImport { opened = false; tgt; _ } ->
          let import_name = String.concat ~sep:"." (as_list tgt) in

          (* Step 1: Check if import_name is a qualified name *)
          if String.contains import_name '.' then
            let qualified_name = module_name ^ "." ^ import_name in
            (* Try finding in current module's nested *)
            match Hashtbl.find non_opened_imports_or_nested qualified_name with
            | Some _ -> add_module_and_nested_to_non_opened qualified_name
            | None ->
              (* If not found in current nested, proceed to ancestor and global search *)
              (match find_in_ancestor_nested module_name import_name builder_instance with
              | Some ancestor_nested_full_name -> add_module_and_nested_to_non_opened ancestor_nested_full_name
              | None -> add_module_and_nested_to_non_opened import_name)
          else
            (* If not a qualified name, directly search in ancestor's nested or globally *)
            (match find_in_ancestor_nested module_name import_name builder_instance with
            | Some ancestor_nested_full_name -> add_module_and_nested_to_non_opened ancestor_nested_full_name
            | None -> add_module_and_nested_to_non_opened import_name)
        | _ -> ()
      );

      (* Add nested modules *)
      let module_prefix = module_name ^ "." in
      List.iter !(module_table.nested) ~f:(fun nested_module_name ->
        add_nested_modules_to non_opened_imports_or_nested nested_module_name builder_instance module_prefix
      )
    ;;


    (* Call this function to find all visible datatype/type decls for a module from the global type table *)
    let find_visible_decls builder_instance module_name =
      match Hashtbl.find builder_instance.decls_table module_name with
      | Some module_table ->
          let self_decls = find_self_decls module_table in
          let non_opened_imports_or_nested = Hashtbl.create (module String) in
          let opened_imports = find_opened_imports builder_instance module_name module_table non_opened_imports_or_nested in
          find_non_opened_imports_or_nested builder_instance module_name module_table non_opened_imports_or_nested;
          let result = { self_decls; opened_imports; non_opened_imports_or_nested } in
          cache_visible_decls result;
          Some result
      | None -> None


    let find_type_in_visible_decls_by_name visible_decls type_name =
      let find_in_module_decls decls_table type_name =
        List.find decls_table ~f:(fun decl ->
          match snd decl with
          | Syntax.ParserPass.TopDecl.DatatypeDecl (_, _, id, _, _) 
          | Syntax.ParserPass.TopDecl.SynonymTypeDecl { id; _ } -> String.equal id type_name
          | _ -> false
        )
      in

      (* 1. Search in self_decls first *)
      match find_in_module_decls visible_decls.self_decls type_name with
      | Some decl -> Some ("self", decl)  (* If found, return "self" as module name, and return decl *)
      | None ->
          (* 2. If not found in self_decls, search in opened_imports *)
          Hashtbl.fold visible_decls.opened_imports ~init:None ~f:(fun ~key:module_name ~data:module_table acc ->
            match acc with
            | Some _ -> acc 
            | None ->
                (* Search for type declaration in the module's decls *)
                match Hashtbl.find module_table.decls type_name with
                | Some decl -> Some (module_name, decl)  
                | None -> None
          )

    let find_qualified_type_decl visible_decls qualified_name =
      (* Helper function to split qualified names into module and type parts *)
      let split_qualified_name qualified_name =
        match String.rsplit2 qualified_name ~on:'.' with
        | Some (module_part, type_part) -> (module_part, type_part)
        | None -> ("", qualified_name)  (* If no '.', assume the whole name is the type name *)
      in

      (* Find type declaration in the given module *)
      let find_in_module_decls module_table type_name =
        Hashtbl.find module_table.decls type_name
      in

      (* Split qualified_name into module_part and type_part *)
      let (module_part, type_part) = split_qualified_name qualified_name in

      (* Use module_part to find the corresponding module in non_opened_imports_or_nested *)
      match Hashtbl.find visible_decls.non_opened_imports_or_nested module_part with
      | Some module_table -> 
          (* After finding the corresponding module, search for type_part and return module name and type declaration *)
          (match find_in_module_decls module_table type_part with
            | Some decl -> Some (module_part, decl) 
            | None -> None)
      | None -> 
          None
    ;;

    (* Find decls of a datatype/type from the visible type table of a current module *)
    let find_type_decl type_name =
      match get_cached_visible_decls () with
      | Some visible_decls -> 
          if String.contains type_name '.' then
            find_qualified_type_decl visible_decls type_name
          else
            find_type_in_visible_decls_by_name visible_decls type_name
      | None ->
          None
    ;;

    (* Check if a type decl exists in the visible type table of a current module *)
    let is_exists type_name =
      match get_cached_visible_decls () with
      | Some _ -> (
          match find_type_decl type_name with
          | Some _ -> true
          | None -> false
        )
      | None -> false
    ;;
    

  end
