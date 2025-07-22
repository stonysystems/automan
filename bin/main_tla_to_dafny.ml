open Core
open Lexing
open Automan

module Printer = 
  Printer.PrettyPrinter(Syntax.TrivMetaData)

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_tla_with_error lexbuf =
  try TlaParser.tla_module TlaLexer.lexeme lexbuf with
  | TlaLexer.SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    exit (-1)
  | TlaParser.Error ->
    fprintf stderr "%a: syntax error\n"  print_position lexbuf;
    exit (-1)

let main tla_filename () =
  let tla = begin
    let inx = In_channel.create tla_filename in
    let lexbuf = Lexing.from_channel inx in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = tla_filename };
    let tla = parse_tla_with_error lexbuf in
    In_channel.close inx;
    tla
  end in
  let dafny = TlaToDafny.translate tla in
  let txt = Printer.print dafny in
  printf "%s\n" (txt)

let () =
Command.basic_spec
  ~summary:"Run automan on Dafny specification and Automan annotation file"
  Command.Spec.(
    empty
    +> anon ("tlaFilename" %: string)
    (* +> anon ("automanFilename" %: string) *)
    (* +> anon ("nameRemappingFilename" %: string) *)
  )
  main
|> Command_unix.run
