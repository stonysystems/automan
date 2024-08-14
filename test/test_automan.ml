open Automan
open Core
open Lexing
open TestCommon


module Translator = Translator.Translator
module Printer    = Printer.PrettyPrinter(Syntax.AnnotationMetaData)

let main dafny_fn automan_fn () =
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
    let dfy' = Translator.translate dfy in
    let str  = Printer.print dfy' in
    printf "%s\n" str

let () =
  Command.basic_spec
    ~summary:"Run automan on Dafny specification and Automan annotation file"
    Command.Spec.(
      empty
      +> anon ("dafnyFilename" %: string)
      +> anon ("automanFilename" %: string)
    )
    main
  |> Command_unix.run
