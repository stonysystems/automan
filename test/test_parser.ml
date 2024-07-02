open Core
open Lexing

let loop _ () = ()

let () =
  Command.basic_spec ~summary:"Parse and display specifications written in Dafny"
  Command.Spec.(empty +> anon ("filename" %: string))
  loop
|> Command_unix.run

