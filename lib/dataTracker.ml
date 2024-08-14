open Syntax
open Internal
open TranslatorCommon


module DataTracker (M : MetaData) = struct

module AST = AST(M)
module TranslatorCommon = TranslatorCommon(M)
module ExprMap = Map.Make(TranslatorCommon.Expr)

class data_tracker 
  (s : AST.Prog.expr_t) (init_dtp : AST.Prog.expr_t) = 
object (self)

  val mutable table         = ExprMap.empty
  val mutable end_point     = TranslatorCommon.expr_blank
  val mutable data_update   = TranslatorCommon.expr_blank
  val mutable this          = s
  val mutable init_dtp      = init_dtp

  method set_table t        = table <- t
  method set_end_point e    = end_point <- e
  method set_data_update e  = data_update <- e
  method set_this e         = 
    if TranslatorCommon.is_expr_blank this then this <- e else ()

  method get_this = this

  method copy = 
    let new_tracker = new data_tracker this init_dtp in 
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

  method is_end_point_filled : bool = 
    TranslatorCommon.is_expr_n_blank end_point

  method is_data_update_filled : bool = 
    TranslatorCommon.is_expr_n_blank data_update

  method is_init_dtp_filled : bool = TranslatorCommon.is_expr_n_blank init_dtp

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
          TranslatorCommon.expr_lst_to_dot_expr prefix_list in
        (* TranslatorCommon.debug_print_expr prefix_expr; *)
        (* checking *)
        assert (
          (TranslatorCommon.is_expr_blank this) ||
          (TranslatorCommon.is_expr_eq this prefix_expr)
        );
        self#set_this prefix_expr;
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
      TranslatorCommon.expr_lst_to_dot_expr prefix_list in
    match suffix_list with
    | [] -> begin
        (* checking *)
        assert (TranslatorCommon.is_expr_blank end_point);
        (* assert (TranslatorCommon.is_expr_blank this); *)
        self#set_this prefix_expr;
        end_point <- value;
      end
    | h :: _ -> begin
        (* checking *)
        (* assert (
          (TranslatorCommon.is_expr_blank this) ||
          (TranslatorCommon.is_expr_eq this prefix_expr)
        ); *)
        self#set_this prefix_expr;
        match ExprMap.find_opt h table with
        | Some entry -> entry#add prefix_list suffix_list value
        | None -> begin
          let new_entry = 
            new data_tracker 
              TranslatorCommon.expr_blank TranslatorCommon.expr_blank in
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
    TranslatorCommon.expr_lst_to_dot_expr prefix_list in
  let rec replace_dot_expr_starts_with_s' 
    (e : AST.Prog.expr_t) : AST.Prog.expr_t = 
    (* TranslatorCommon.debug_print_expr e; *)
    if (TranslatorCommon.is_expr_tp_aug_dot e) then
      let e_lst = TranslatorCommon.dot_expr_to_expr_lst e in
      let e_lst = NonEmptyList.coerce e_lst in 
      let h, rest = NonEmptyList.uncons e_lst in
      match (TranslatorCommon.is_expr_eq h s') with
      | true -> root_entry#query_member_wrapper (s :: rest)
      | false -> e
    else if (TranslatorCommon.is_expr_tp_data_update e) then
      let x, suffix = TranslatorCommon.expr_to_suffix e in
      let member_binding_upd_lst = 
        TranslatorCommon.suffix_to_data_update suffix in
      let rec aux lst = 
        match lst with
        | [] -> []
        | h :: rest -> begin 
            [
              let assignee, v = h in
              (assignee, replace_dot_expr_starts_with_s' v)
            ] @ aux rest
        end
      in
      let member_binding_upd_lst' = aux member_binding_upd_lst in
      let member_binding_upd_lst' = 
        NonEmptyList.coerce member_binding_upd_lst' in
      AST.Prog.Suffixed(x, DataUpd(member_binding_upd_lst'))
    else
      e
  in
  match suffix_list with
  | [] -> begin
    assert (TranslatorCommon.is_expr_blank data_update);
    self#set_this prefix_expr;
    data_update <- replace_dot_expr_starts_with_s' value;
  end
  | h :: _ -> begin 
    (* checking *)
    assert (
      (TranslatorCommon.is_expr_blank this) ||
      (TranslatorCommon.is_expr_eq this prefix_expr)
    );
    self#set_this prefix_expr;
    match ExprMap.find_opt h table with
    | Some entry -> entry#add prefix_list suffix_list value
    | None -> begin
      let new_entry = 
        new data_tracker 
          TranslatorCommon.expr_blank TranslatorCommon.expr_blank in
      new_entry#add_data_update prefix_list suffix_list value root_entry s s';
      self#add_helper h new_entry
    end
  end    

  method add_data_update_wrapper
  (suffix_list  : AST.Prog.expr_t list)
  (value        : AST.Prog.expr_t)
  (root_entry   : data_tracker)
  (s            : AST.Prog.expr_t)
  (s'           : AST.Prog.expr_t) : unit = 
    (* TranslatorCommon.debug_print_expr value; *)
    self#add_data_update [] suffix_list value root_entry s s'

  method construct = 
    let x = begin
      match self#is_data_update_filled with 
      | true -> data_update
      | false -> begin
        match self#is_end_point_filled with 
        | true -> end_point
        | false -> begin
          match self#is_init_dtp_filled with 
          | false -> begin
            let rec aux lst = 
              match lst with 
              | [] -> []
              | (k, v) :: lst -> begin
                let k_id = TranslatorCommon.expr_to_id k in
                let k_id_either : (id_t, int) Either.t = Left k_id in
                let member_binding_upd = (k_id_either, v#construct) in
                [member_binding_upd] @ (aux lst)
              end
            in
            let bindings = ExprMap.bindings table in
            let kv_list = aux bindings in 
            let kv_list = NonEmptyList.coerce kv_list in
            AST.Prog.Suffixed(this, DataUpd(kv_list))
          end
          | true -> begin 
            (*  *)
            assert false
          end end end end in x

end ;;

end
