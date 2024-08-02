open Syntax
open Internal
open TranslatorCommon


module DataTracker (M : MetaData) = struct

module AST = AST(M)
module TranslatorCommon = TranslatorCommon(M)
module Expr = struct 
  type t = AST.Prog.expr_t
  let compare e1 e2 = 
    let e1_str = TranslatorCommon.str_of_expr e1 in
    let e2_str = TranslatorCommon.str_of_expr e2 in 
    if e1_str = e2_str then 0 
    else if e1_str < e2_str then -1 
    else 1
end ;;

module ExprMap = Map.Make(Expr)

class data_tracker = 
object 
  val mutable table         = ExprMap.empty
  val mutable end_point     = TranslatorCommon.expr_blank
  val mutable data_update   = TranslatorCommon.expr_blank
  val mutable this          = TranslatorCommon.expr_blank

  method set_table t        = table <- t
  method set_end_point e    = end_point <- e
  method set_data_update e  = data_update <- e
  method set_this e         = this <- e

  method add_to_table 
    (k : AST.Prog.expr_t) (v : data_tracker) = 
    ExprMap.add k v table

  method copy = 
    let new_tracker = new data_tracker in 
    let new_table = begin
      ExprMap.fold (
        fun k v acc -> ExprMap.add k (v#copy) acc
       ) table ExprMap.empty
    end in
    new_tracker#set_table new_table;
    new_tracker#set_end_point end_point;
    new_tracker#set_data_update data_update;
    new_tracker#set_this this;
    new_tracker

  method is_end_point_filled = TranslatorCommon.is_expr_neq end_point

  method is_data_update_filled = 
    TranslatorCommon.is_expr_neq data_update

  method query_member 
    (prefix_list : AST.Prog.expr_t list)
    (suffix_list : AST.Prog.expr_t list) : AST.Prog.expr_t = 
    let prefix_list, suffix_list = begin
      let suffix_list = NonEmptyList.coerce suffix_list in
      let suffix_list, h = NonEmptyList.unsnoc suffix_list in
      let prefix_list = prefix_list @ [h] in
      prefix_list, suffix_list
    end in
    match suffix_list with
    | [] -> end_point (* Should check of the end_point has been assigned before *)
    | h :: _ -> begin
        let c1 
      end

end ;;

end
