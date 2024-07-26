open Automan
open Core
open Lexing
open TestCommon

let parse_dafny_and_print lexbuf =
  let x = parse_dafny_with_error lexbuf in
  printf "%s\n" Syntax.ParserPass.(show x)

let parse_annotations_and_print lexbuf =
  let x = parse_annotations_with_error lexbuf in
  printf "%s\n" (Syntax.Annotation.show_toplevel_t x)

let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  if Filename.check_suffix filename ".dfy" then
    parse_dafny_and_print lexbuf
  else if Filename.check_suffix filename ".automan" then
    parse_annotations_and_print lexbuf
  else
    ();
  In_channel.close inx

let () =
  Command.basic_spec ~summary:"Parse and display specification ASTs written in Dafny"
    Command.Spec.(empty +> anon ("filename" %: string))
    loop
  |> Command_unix.run

