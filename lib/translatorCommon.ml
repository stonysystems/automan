open Syntax
open Printer
open Internal


(**
  *  
  *
  *)

module TranslatorCommon (M : MetaData) = struct 
  module AST = AST(M)
  module Printer = PrettyPrinter(M)

  let expr_to_suffix (e : AST.Prog.expr_t) = 
    match e with
    | Suffixed (x, suffix) -> (x, suffix)
    | _ -> assert false

  let suffix_to_dot_id (x : AST.Prog.suffix_t) : AST.Prog.expr_t = 
    match x with 
    | AugDot augmented_dotsuffix -> begin
      let dotsuffix, _ = augmented_dotsuffix in
      match dotsuffix with 
      | DSId id -> AST.Prog.NameSeg(id, [])
      | _ -> assert false
    end
    | _ -> assert false

  let suffix_to_data_update (x : AST.Prog.suffix_t) = 
    match x with 
    | DataUpd member_binding_upd_lst -> begin
      NonEmptyList.as_list member_binding_upd_lst
    end
    | _ -> assert false
  
  let is_expr_tp_aug_dot (e : AST.Prog.expr_t) = 
    match e with 
    | Suffixed (_, suffix) -> begin
      match suffix with
      | AugDot _ -> true
      | _ -> false
    end
    | _ -> false
  
  let is_expr_tp_data_update (e : AST.Prog.expr_t) = 
    match e with 
    | Suffixed (_, suffix) -> begin
      match suffix with
      | DataUpd _ -> true
      | _ -> false
    end
    | _ -> false

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

  let is_expr_n_blank e = 
    not (is_expr_eq e expr_blank)

  let expr_to_id (e : AST.Prog.expr_t) : id_t = 
    match e with 
    | NameSeg name_seg -> begin
      let id, _ = name_seg in id
    end
    | _ -> assert false

  let move_one_expr_from_suffix_to_prefix prefix_list suffix_list =
    let suffix_list = NonEmptyList.coerce suffix_list in
    let suffix_list, h = NonEmptyList.unsnoc suffix_list in
    let prefix_list = prefix_list @ [h] in
    prefix_list, suffix_list
  
  let convert_expr_lst_to_dot_expr
    (lst : AST.Prog.expr_t list) : AST.Prog.expr_t = 
    let lst = NonEmptyList.coerce lst in
    NonEmptyList.fold_left_1 begin
      fun l r ->
        (* checking *)
        let r_id = expr_to_id r in
        Suffixed (
          l, 
          AugDot (DSId(r_id), [])
        )
    end lst
  
  (* The expr occured can only be id *)  
  let convert_dot_expr_to_expr_lst (x : AST.Prog.expr_t) = 
    let rec aux x = 
      match is_expr_tp_aug_dot x with
      | true -> begin
        let x, suffix = expr_to_suffix(x) in
        (aux x) @ [suffix_to_dot_id suffix]
      end
      | false -> begin
        let _ = expr_to_id x in
        [x]
      end
    in
    aux x

end
