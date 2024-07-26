open Core
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_dafny_with_error lexbuf =
  try DafnyParser.dafny Lexer.lexeme lexbuf with
  | Lexer.SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    exit (-1)
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

