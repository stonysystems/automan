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
object (self)
  val mutable table         = ExprMap.empty
  val mutable end_point     = TranslatorCommon.expr_blank
  val mutable data_update   = TranslatorCommon.expr_blank
  val mutable this          = TranslatorCommon.expr_blank

  method set_table t        = table <- t
  method set_end_point e    = end_point <- e
  method set_data_update e  = data_update <- e
  method set_this e         = this <- e

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

  method add_helper 
    (k : AST.Prog.expr_t) (v : data_tracker) : unit = 
    match (ExprMap.mem k table) with
    | true -> assert false (* checking *)
    | false -> table <- ExprMap.add k v table

  method is_end_point_filled = TranslatorCommon.is_expr_neq end_point

  method is_data_update_filled = 
    TranslatorCommon.is_expr_neq data_update

  method query_member 
    (prefix_list : AST.Prog.expr_t list)
    (suffix_list : AST.Prog.expr_t list) : AST.Prog.expr_t = 
    let prefix_list, suffix_list = 
      TranslatorCommon.move_one_expr_from_suffix_to_prefix 
        prefix_list suffix_list in
    match suffix_list with
    | [] -> begin
        (* checking *)
        assert (TranslatorCommon.is_expr_n_blank end_point);
        end_point
      end
    | h :: _ -> begin
        let prefix_expr = 
          TranslatorCommon.convert_expr_lst_to_dot_expr prefix_list in
        (* checking *)
        assert (
          (TranslatorCommon.is_expr_blank this) ||
          (TranslatorCommon.is_expr_eq this prefix_expr)
        );
        this <- prefix_expr;
        match ExprMap.find_opt h table with
        | Some entry -> entry#query_member prefix_list suffix_list
        | None -> assert false
      end

  method query_member_wrapper suffix_list = 
    self#query_member [] suffix_list

  method add 
    (prefix_list : AST.Prog.expr_t list)
    (suffix_list : AST.Prog.expr_t list)
    (value : AST.Prog.expr_t) : unit =
    let prefix_list, suffix_list = 
      TranslatorCommon.move_one_expr_from_suffix_to_prefix 
        prefix_list suffix_list in 
    let prefix_expr = 
      TranslatorCommon.convert_expr_lst_to_dot_expr prefix_list in
    match suffix_list with
    | [] -> begin
        (* checking *)
        assert (TranslatorCommon.is_expr_n_blank end_point);
        assert (TranslatorCommon.is_expr_blank this);
        this <- prefix_expr;
        end_point <- value;
      end
    | h :: _ -> begin
        (* checking *)
        assert (
          (TranslatorCommon.is_expr_blank this) ||
          (TranslatorCommon.is_expr_eq this prefix_expr)
        );
        this <- prefix_expr;
        match ExprMap.find_opt h table with
        | Some entry -> entry#add prefix_list suffix_list value
        | None -> begin
          let new_entry = new data_tracker in
          new_entry#add prefix_list suffix_list value;
          self#add_helper h new_entry
        end
    end

  method add_wrapper suffix_list value = 
    self#add [] suffix_list value

  method add_data_update 
  (prefix_list  : AST.Prog.expr_t list)
  (suffix_list  : AST.Prog.expr_t list)
  (value        : AST.Prog.expr_t)
  (root_entry   : data_tracker)
  (s            : AST.Prog.expr_t)
  (s'           : AST.Prog.expr_t) : unit = 
  let prefix_list, suffix_list = 
  TranslatorCommon.move_one_expr_from_suffix_to_prefix 
    prefix_list suffix_list in 
  let prefix_expr = 
    TranslatorCommon.convert_expr_lst_to_dot_expr prefix_list in
  let rec replace_dot_expr_starts_with_s' 
    (e : AST.Prog.expr_t) : AST.Prog.expr_t = 
    if (TranslatorCommon.ExprTypeHelper.is_expr_tp_aug_dot e) then
      let e_lst = TranslatorCommon.convert_dot_expr_to_expr_lst e in
      let e_lst = NonEmptyList.coerce e_lst in 
      let rest, h = NonEmptyList.unsnoc e_lst in
      match (TranslatorCommon.is_expr_eq h s') with
      | true -> root_entry#query_member_wrapper (s :: rest)
      | false -> e
    else if (TranslatorCommon.ExprTypeHelper.is_expr_tp_data_update e) then
      e
    else
      e
  in
  match suffix_list with
  | [] -> begin
    assert (TranslatorCommon.is_expr_blank data_update);
    this <- prefix_expr;
  end
  | h :: _ -> begin 
    (* checking *)
    assert (
      (TranslatorCommon.is_expr_blank this) ||
      (TranslatorCommon.is_expr_eq this prefix_expr)
    );
    this <- prefix_expr;
    match ExprMap.find_opt h table with
    | Some entry -> entry#add prefix_list suffix_list value
    | None -> begin
      let new_entry = new data_tracker in
      new_entry#add_data_update prefix_list suffix_list value root_entry s s';
      self#add_helper h new_entry
    end
  end

end ;;

end
