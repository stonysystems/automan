open Automan


module AST = Syntax.AST(Syntax.AnnotationMetaData)
module DataTracker = DataTracker.DataTracker(Syntax.AnnotationMetaData)
module Printer = Printer.PrettyPrinter(Syntax.AnnotationMetaData)
module TranslatorCommon = 
  TranslatorCommon.TranslatorCommon(Syntax.AnnotationMetaData)

let id_to_expr (x : Syntax.id_t) = AST.Prog.NameSeg((x, []))

let print data_tracker = 
  let x = data_tracker#construct in
  let x_str = Printer.Prog.print_expr_in_one_line x in
  print_endline x_str

let test1 = 
  let data_tracker = new DataTracker.data_tracker (id_to_expr "s") in
  data_tracker#add_wrapper [id_to_expr "s'"] (id_to_expr "s");
  print data_tracker

let test2 = 
  let data_tracker = new DataTracker.data_tracker (id_to_expr "s") in
  data_tracker#add_wrapper 
    [(id_to_expr "s'");(id_to_expr "a")] (id_to_expr "x");
  data_tracker#add_wrapper 
    [(id_to_expr "s'");(id_to_expr "b")] (id_to_expr "y");
  print data_tracker

let test3 = 
  let data_tracker = new DataTracker.data_tracker (id_to_expr "s") in
  data_tracker#add_wrapper 
    [(id_to_expr "s'");(id_to_expr "a")] (id_to_expr "x");
  data_tracker#add_data_update_wrapper 
    [(id_to_expr "s'")] 
    (AST.Prog.Suffixed((id_to_expr "s"), DataUpd(
      Internal.NonEmptyList.coerce (
        [
          (let x : (Syntax.id_t, int) Either.t = Left "a" in x,
            TranslatorCommon.convert_expr_lst_to_dot_expr [
              (id_to_expr "s'");
              (id_to_expr "a")
            ]);
          (let x : (Syntax.id_t, int) Either.t = Left "b" in x,
            TranslatorCommon.convert_expr_lst_to_dot_expr [
              (id_to_expr "s");
              (id_to_expr "b")
            ]);
        ]
      )))) 
    data_tracker (id_to_expr "s") (id_to_expr "s'");
  print data_tracker

let () = test1 
let () = test2
let () = test3
