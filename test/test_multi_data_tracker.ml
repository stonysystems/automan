open Automan


module AST = Syntax.AST(Syntax.AnnotationMetaData)
module DataTracker = DataTracker.DataTracker
module Printer = Printer.PrettyPrinter(Syntax.AnnotationMetaData)
module TranslatorCommon = TranslatorCommon.TranslatorCommon
module MultiDataTracker = MultiDataTracker.MultiDataTracker

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
