open Automan
open Core
open Stdlib
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_dafny_with_error lexbuf =
  try DafnyParser.file_level Lexer.lexeme lexbuf with
  | Lexer.SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | DafnyParser.Error ->
    fprintf stderr "%a: syntax error\n"  print_position lexbuf;
    exit (-1)

let parse_annotations_with_error lexbuf =
  try AnnotationParser.toplevel Lexer.lexeme lexbuf with
  | Lexer.SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    exit (-1)
  | AnnotationParser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let rec parse_dafny_and_print lexbuf =
  match parse_dafny_with_error lexbuf with
  | Some x ->
    printf "%s\n" Syntax.ParserPass.FileLevel.(show x);
    parse_dafny_and_print lexbuf
  | None -> ()

let parse_annotations_and_print lexbuf =
  let x = parse_annotations_with_error lexbuf in
  printf "%s\n" (Syntax.AutoMan.show_toplevel_t x)

let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  if String.ends_with ~suffix:"dfy" filename then
    parse_dafny_and_print lexbuf
  else if String.ends_with ~suffix:"automan" filename then
    parse_annotations_and_print lexbuf
  else
    ();
  In_channel.close inx

let () =
  Command.basic_spec ~summary:"Parse and display specifications written in Dafny"
    Command.Spec.(empty +> anon ("filename" %: string))
    loop
  |> Command_unix.run

