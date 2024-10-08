open Automan
open Core
open Lexing
open TestCommon
open Checker
open TypeTableBuilder


module Translator = Translator.Translator
module Printer = 
  Printer.PrettyPrinter(TranslatorMetadata.TranslationMetaData)


let main dafny_fn automan_fn () =

  let type_table = TypeTableBuilder.create () in
  let _ = TypeTableBuilder.build_type_table dafny_fn type_table in

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
    let (dfy_moded, log) = Moder.run dfy in
    let _ = log in 
    let dfy_checked = Checker.check dfy_moded type_table in
    let generated_code = Translator.translate dfy_checked type_table in
    let str = Printer.print generated_code in
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
