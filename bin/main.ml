open Automan
open Core
open Internal

module RunParser = struct
  open Lexing

  (* Aborts on parser error *)
  let automan (fn: string): Syntax.Annotation.t list =
    let inx = In_channel.create fn in
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fn };

    TestCommon.parse_annotations_with_error lexbuf

  let dafny (fn: string): (Syntax.ParserPass.t, string) Result.t =
    let inx = In_channel.create fn in
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fn };

    TestCommon.parse_dafny_return_error lexbuf
end

module Util = struct
  let read_dir_recursive (dir: string): string list =
    let rec aux dir depth =
      if depth < 100 then begin
        Sys_unix.ls_dir dir
        |> List.concat_map begin fun fn ->
          let full_fn = Filename.concat dir fn in
          if Sys_unix.is_directory_exn full_fn then
            aux full_fn (depth + 1)
          else
            [fn]
        end
      end else
        failwith "automan: [ERROR] max project depth reached"
    in
    aux dir 0

  let find_dafny_fn_for_automan
      (dafny_fns: string list) (automan_fn: string): string =
    let res =
      Core.List.find dafny_fns ~f:begin fun dafny_fn ->
        String.is_prefix
          ~prefix:(Filename.chop_extension automan_fn)
          dafny_fn
      end
    in
    match res with
    | None ->
      failwith
        ("automan: [ERROR] found annotation file without corresponding Dafny file: "
         ^ automan_fn)
    | Some res -> res

  let ensure_impl_dir (impl_dir: string): unit =
    if Sys_unix.is_directory_exn impl_dir then
      ()
    else if not (Sys_unix.file_exists_exn impl_dir) then
      Core_unix.mkdir impl_dir
    else
      failwith
        ("automan: [ERROR] IMPL_DIR exists and is a regular file: "
         ^ impl_dir)

  let dafny_tgt_fn (impl_dir: string) (dafny_fn: string): string =
    let (prefix, suffix) = Core.String.lsplit2_exn ~on:'.' dafny_fn in

    Filename.concat impl_dir
      (prefix ^ "_Impl." ^ suffix)
end

let automan_pipeline
    (spec_dir: string) (impl_dir: string)
    (anns: Syntax.Annotation.toplevel_t)
    (dafny_fn: string): unit =

  let dafny_impl_fn = Util.dafny_tgt_fn impl_dir dafny_fn in

  begin
    let ( let* ) = Result.bind in

    let* () =
      Result.error_when         (* Not an error, just early return *)
        (Sys_unix.file_exists_exn dafny_impl_fn)
        begin lazy
          ("automan: [INFO] file exists, skipping: " ^ dafny_impl_fn)
        end
    in

    let* dafny_ast =
      RunParser.dafny (Filename.concat spec_dir dafny_fn) in

    let* dafny_ann =
      Annotator.annotate anns dafny_ast in

    let (_dafny_mod, _log) = Moder.run dafny_ann in

    Result.Ok ()
  end
  |> Result.fold
    ~ok:(Fun.const ())
    ~error:(printf "%s\n")

let main spec_dir impl_dir _overwrite () =
  let (automans, dafnys) = begin
    Util.read_dir_recursive spec_dir
    |> List.filter_map begin fun fn ->
      if Filename.check_suffix fn ".automan" then
        Option.Some (Either.Left fn)
      else if Filename.check_suffix fn ".dfy" then
        Option.Some (Either.Right fn)
      else
        Option.None
    end
    |> List.partition_map Fun.id
  end in

  printf "automan: [LOG ] annotation files found: %s\n"
    Internal.List.(show Format.pp_print_string automans);

  let translate_srcs =
    List.map (Util.find_dafny_fn_for_automan dafnys) automans
  in

  printf "automan: [LOG ] translation sources found: %s\n"
    Internal.List.(show Format.pp_print_string translate_srcs);

  let compiled_automans =
    automans
    |> List.concat_map begin fun fn ->
      let full_fn = Filename.concat spec_dir fn in
      RunParser.automan full_fn
    end
  in

  Util.ensure_impl_dir impl_dir;

  translate_srcs
  |> List.iter (automan_pipeline spec_dir impl_dir compiled_automans)

let () =
  Command.basic_spec
    ~summary:"Tool for automatically generating implementations from Dafny protocol specifications"
    Command.Spec.(
      empty
      +> anon ("SPEC_DIR" %: string)
      +> anon ("IMPL_DIR" %: string)
      +> flag ~doc:"Overwrite these implementation files, if they exist"
        "--overwrite" (optional string)
    )
    main
  |> Command_unix.run
