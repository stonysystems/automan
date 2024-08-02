open Syntax
open Printer

module TranslatorCommon (M : MetaData) = struct 
  module AST = AST(M)
  module Printer = PrettyPrinter(M)

  let str_of_expr (e : AST.Prog.expr_t) : string = 
    Printer.Prog.(print_expr_in_one_line e)

  let expr_blank = AST.Prog.NameSeg ("", []) 

  let is_expr_eq e1 e2 = 
    let str_e1 = str_of_expr e1 in
    let str_e2 = str_of_expr e2 in
    str_e1 = str_e2
  
  let is_expr_neq e1 e2 = 
    not (is_expr_eq e1 e2)

  let is_expr_blank e = 
    is_expr_eq e expr_blank

end

