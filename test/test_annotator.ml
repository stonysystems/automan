open Automan
open Core
open Lexing
open TestCommon

let main dafny_fn automan_fn () =
  let dafny_basename = Filename.basename dafny_fn in
  let annotator_filename = dafny_basename ^ ".annotator" in

  (* Dafny *)
  let dafny = begin
    let inx = In_channel.create dafny_fn in
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = dafny_fn };
    let dafny = parse_dafny_with_error lexbuf in
    In_channel.close inx;
    dafny
  end in
  let ann = begin
    let inx = In_channel.create automan_fn in
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = automan_fn };
    let ann = parse_annotations_with_error lexbuf in
    In_channel.close inx;
    ann
  end in
  match Annotator.annotate ann dafny with
  | Result.Error msg ->
    printf "Error: %s\n" msg
  | Result.Ok    dfy ->
    Out_channel.with_file annotator_filename ~f:(fun out ->
      Out_channel.output_string out (Annotator.AnnotationPass.show dfy)
    );
    printf "Annotator pass output has been written to %s\n" annotator_filename

let () =
  Command.basic_spec
    ~summary:"Run annotator on Dafny specification and Automan annotation file, printing the resulting AST"
    Command.Spec.(
      empty
      +> anon ("dafnyFilename" %: string)
      +> anon ("automanFilename" %: string)
    )
    main
  |> Command_unix.run
