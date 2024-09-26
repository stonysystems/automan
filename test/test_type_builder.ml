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
      printf "Declaration: %s\n\n" (Syntax.ParserPass.TopDecl.show decl)
    )
  )

let main dafny_fn () =
  let builder_instance = TypeTableBuilder.create () in
  let _ = TypeTableBuilder.build_type_table dafny_fn builder_instance in
  
  (* Print the entire type table *)
  print_type_table builder_instance;

  printf "\n--- Testing find imports of a module ---\n";
  let imports = TypeTableBuilder.find_module_imports builder_instance "LiveRSL__Configuration_i" in
  List.iter imports ~f:(fun import_decl ->
    printf "Found ModuleImport: %s\n" (Syntax.ParserPass.TopDecl.show import_decl)
  );


  printf "\n--- Testing find all by type name ---\n";
  let decls = TypeTableBuilder.find_all_type_decls_by_type_name builder_instance "Ballot" in
  if List.is_empty decls then
    printf "No declarations found by type name\n"
  else
    List.iter decls ~f:(fun (module_name, decl) ->
      printf "Found in module %s: %s\n" module_name (Syntax.ParserPass.TopDecl.show decl)
    );

  printf "\n--- Testing when multiple type with same name, use import lists to identify correct one ---\n";
  let results = TypeTableBuilder.find_type_decl_by_type_name_with_imports builder_instance "Ballot" "LiveRSL__Configuration_i" in
  if List.is_empty results then
    printf "No open declarations found for Ballot\n"
  else
    List.iter results ~f:(fun (module_name, decl) ->
      printf "Found in module %s: %s\n" module_name (Syntax.ParserPass.TopDecl.show decl)
    );

  printf "\n--- Testing find_type_decl_by_module_and_type_name_with_imports ---\n";
  match TypeTableBuilder.find_type_decl_by_module_and_type_name_with_imports builder_instance "Ballot" "E" "LiveRSL__Configuration_i" with
  | Some (module_name, decl) -> 
      printf "Found by module and type with imports in module %s: %s\n" module_name (Syntax.ParserPass.TopDecl.show decl)
  | None -> printf "Declaration not found by module and type with imports\n";

  printf "\n--- Testing find by module and type name ---\n";
  match TypeTableBuilder.find_type_decl_by_module_and_type_name builder_instance "LiveRSL__Acceptor_i" "LAcceptor" with
  | Some (module_name, decl) -> printf "Found in module %s: %s\n" module_name (Syntax.ParserPass.TopDecl.show decl)
  | None -> printf "Declaration not found\n"

let () =
  Command.basic_spec
    ~summary:"Build type table for a Dafny file."
    Command.Spec.(
      empty
      +> anon ("dafnyFilename" %: string)
    )
    main
  |> Command_unix.run