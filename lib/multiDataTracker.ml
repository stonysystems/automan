open Syntax
open TranslatorCommon
open DataTracker


module MultiDataTracker (M : MetaData) = struct 

module AST = AST(M)
module TranslatorCommon = TranslatorCommon(M)
module DataTracker = DataTracker(M)
module ExprMap = Map.Make(TranslatorCommon.Expr)

class multi_data_tracker = 
object
  val mutable table = ExprMap.empty

  method set_table t = table <- t

  method register 
    (s : AST.Prog.expr_t) (s' : AST.Prog.expr_t) (init_dtp : AST.Prog.expr_t) = 
    let new_tracker = new DataTracker.data_tracker s init_dtp in 
    let table' = ExprMap.add s' new_tracker table in
    table <- table'
  
  method add
    (s' : AST.Prog.expr_t) 
    (suffix_list  : AST.Prog.expr_t list) 
    (value : AST.Prog.expr_t) = 
  match ExprMap.find_opt s' table with 
  | Some entry -> begin
    let s = entry#get_this in
    match TranslatorCommon.is_expr_tp_data_update value with
    | true -> entry#add_data_update_wrapper suffix_list value entry s s'
    | false -> entry#add_wrapper suffix_list value
  end
  | None -> assert false

  method construct = 
    let rec aux lst = 
      match lst with 
      | [] -> []
      | (_, v) :: lst -> begin
        v#construct :: (aux lst)
      end in
    let bindings = ExprMap.bindings table in 
    let items = aux bindings in
    AST.Prog.Tuple items

  method copy = 
    let new_multi_tracker = new multi_data_tracker in
    let new_table = begin 
      ExprMap.fold (
        fun k v acc -> ExprMap.add k (v#copy) acc
       ) table ExprMap.empty
    end in
    new_multi_tracker#set_table new_table;
    new_multi_tracker

end
end 
