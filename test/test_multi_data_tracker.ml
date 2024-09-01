open Automan
open Syntax


module AST = AST(Annotator.AnnotationMetaData)
module Refinement = Refinement.Refinement
module TCommon = TranslatorCommon.TranslatorCommon
module Printer = Printer.PrettyPrinter(Annotator.AnnotationMetaData)


let id_to_expr (x : Syntax.id_t) = AST.Prog.NameSeg((x, []))

let print data_tracker = 
  let x = data_tracker#construct in
  let x_str = Printer.Prog.print_expr_in_one_line x in
  print_endline x_str

let test1 = 
  let multi_data_tracker = new MultiDataTracker.multi_data_tracker in 
  let expr_blank = TranslatorCommon.expr_blank in
  multi_data_tracker#register (id_to_expr "s") (id_to_expr "s'") expr_blank;
  multi_data_tracker#register (id_to_expr "x") (id_to_expr "x'") expr_blank;
  multi_data_tracker#add 
    (id_to_expr "s'") 
    [(id_to_expr "s'");(id_to_expr "a")] (id_to_expr "a'");
  multi_data_tracker#add 
    (id_to_expr "x'") 
    [(id_to_expr "x'");(id_to_expr "b")] (id_to_expr "b'");
  print multi_data_tracker

let () = test1 
