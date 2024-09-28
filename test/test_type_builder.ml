open Automan
open Core
open TypeTableBuilder


let print_type_table builder_instance =
  printf "Type Table Contents:\n";

  Hashtbl.iteri builder_instance.TypeTableBuilder.decls_table ~f:(fun ~key:module_name ~data:module_table ->
    printf "Module: %s\n" module_name;
    List.iter !(module_table.imports) ~f:(fun import_decl ->
      printf "Import: %s\n" (Syntax.ParserPass.TopDecl.show import_decl)
    );
    Hashtbl.iteri module_table.decls ~f:(fun ~key:id ~data:decl ->
      printf "ID: %s\n" id;
      printf "Declaration: %s\n" (Syntax.ParserPass.TopDecl.show decl)
    );

    printf "Nested Modules:\n";
    List.iter !(module_table.nested) ~f:(fun nested_module_name ->
      printf "%s\n" nested_module_name
    );

    printf("\n")
  )

let main dafny_fn module_name type_name () =
  let builder_instance = TypeTableBuilder.create () in
  begin
    printf ">>>> BEGIN build_type_table >>>>>>>>>>>>>>>>>>>>>>\n";
    let _ = TypeTableBuilder.build_type_table dafny_fn builder_instance in
    printf "<<<< END   build_type_table <<<<<<<<<<<<<<<<<<<<<<\n"
  end;

  (* Print the entire type table *)
  begin
    printf ">>>> BEGIN print_type_table >>>>>>>>>>>>>>>>>>>>>>\n";
    print_type_table builder_instance;
    printf "<<<< END   print_type_table <<<<<<<<<<<<<<<<<<<<<<\n"
  end;

  (* printf "\n--- Testing find visible decls ---\n";
  let visible_decls = TypeTableBuilder.find_visible_decls builder_instance "LiveRSL__Acceptor_i" in
  match visible_decls with
  | Some decls ->
    printf "Self Declarations:\n";
    List.iter decls.self_decls ~f:(fun decl ->
      printf "  %s\n" (Syntax.ParserPass.TopDecl.show decl)
    );

    printf "\nOpened Imports (Modules):\n";
    Hashtbl.iteri decls.opened_imports ~f:(fun ~key:module_name ~data:_ ->
      printf "Opened Module: %s\n" module_name;
      (* printf "  Declarations:\n";
      Hashtbl.iteri module_table.TypeTableBuilder.decls ~f:(fun ~key:id ~data:decl ->
        printf "    ID: %s\n" id;
        printf "    Declaration: %s\n" (Syntax.ParserPass.TopDecl.show decl)
      );
      printf "  Imports:\n";
      List.iter !(module_table.TypeTableBuilder.imports) ~f:(fun import_decl ->
        printf "    %s\n" (Syntax.ParserPass.TopDecl.show import_decl)
      );
      printf "  Nested Modules:\n";
      List.iter !(module_table.TypeTableBuilder.nested) ~f:(fun nested_module ->
        printf "    Nested Module: %s\n" nested_module
      ) *)
    );

    printf "\nNon-opened Imports or Nested Modules:\n";
    Hashtbl.iteri decls.non_opened_imports_or_nested ~f:(fun ~key:module_name ~data:module_table ->
      printf "Non-opened or Nested Module: %s\n" module_name;
      printf "  Declarations:\n";
      Hashtbl.iteri module_table.TypeTableBuilder.decls ~f:(fun ~key:id ~data:decl ->
        printf "    ID: %s\n" id;
        printf "    Declaration: %s\n" (Syntax.ParserPass.TopDecl.show decl)
      );
      printf "  Imports:\n";
      List.iter !(module_table.TypeTableBuilder.imports) ~f:(fun import_decl ->
        printf "    %s\n" (Syntax.ParserPass.TopDecl.show import_decl)
      );
      printf "  Nested Modules:\n";
      List.iter !(module_table.TypeTableBuilder.nested) ~f:(fun nested_module ->
        printf "    Nested Module: %s\n" nested_module
      )
    );
  | None -> printf "Module not found.\n"
  ; *)


  (* find all visible types of a module *)
  let _ = TypeTableBuilder.find_visible_decls builder_instance module_name in

  if TypeTableBuilder.is_exists type_name then (
    printf "\nQuerying type\n";

    (* query a type decl in visible types *)
    match TypeTableBuilder.find_type_decl type_name with
    | Some (module_name, (modifiers, decl_body)) ->
        printf "Found in module %s: %s\n" module_name (Syntax.ParserPass.TopDecl.show (modifiers, decl_body))
    | None ->
        printf "Type '%s' not found in visible declarations.\n" type_name
  ) else
    printf "Type '%s' does not exist in visible declarations.\n" type_name



      
let () =
  Command.basic_spec
    ~summary:"Build type table for a Dafny file."
    Command.Spec.(
      empty
      +> anon ("dafnyFilename" %: string)
      +> anon ("moduleName" %: string)
      +> anon ("typeName" %: string)
    )
    main
  |> Command_unix.run
