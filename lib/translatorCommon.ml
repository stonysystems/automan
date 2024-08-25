open Syntax
open Internal


(**
  * **************************************************************************
  * Some helper functions to assist with translation
  * **************************************************************************
  *
  * starts_with
  * replace_prefix
  *
  * expr_to_suffix : AST.Prog.exprt_t -> AST.Prog.Suffixed 
  * suffix_to_dot_id : x.b -> b; b must be a id_t; return as expr_t
  * suffix_to_data_update : Suffix -> member_binding_upd_lst as list
  *
  * is_expr_tp_aug_dot : Whether an expr_t is Suffix with AugDot
  * is_expr_tp_data_update : Whether an expr_t is Suffix with DataUpd
  *
  * is_primitive 
  *
  * debug_print
  * debug_print_expr
  * str_of_expr
  * expr_of_str
  * expr_blank
  * is_expr_eq 
  * is_expr_neq
  * is_expr_blank
  * is_expr_n_blank
  * expr_to_id : expr -> id; The expr must be a id_t
  *
  * id_of_tp
  * tp_of_id
  * id_and_gen_inst_of_tp
  *
  * move_one_expr_from_suffix_to_prefix: 
  *                     h :: suffix, prefix -> suffix, preffix @ [h]
  * expr_lst_to_dot_expr : [a, b, c, d] -> a.b.c.d
  * dot_expr_to_expr_lst : a.b.c.d -> [a, b, c, d]
  * expr_lst_to_and
  * **************************************************************************
  *)

module AST = AnnotationPass
module Printer = Printer.PrinterAnnotation

module TranslatorCommon = struct 

  let starts_with s prefix =
    let len_s = String.length s in
    let len_prefix = String.length prefix in
    len_s >= len_prefix && String.sub s 0 len_prefix = prefix

  let replace_prefix str old_prefix new_prefix =
    let len_old = String.length old_prefix in
    if String.length str >= len_old && String.sub str 0 len_old = old_prefix then
      new_prefix ^ String.sub str len_old (String.length str - len_old)
    else
      str

  let is_primitive id = 
    List.exists (fun x -> x = id)
      [ "int"; "bool"; "nat"; "string" ] 

  let is_built_in_collection id = 
    List.exists (fun x -> x = id)
    [ "seq"; "set"; "map" ] 

  let id_and_gen_inst_of_tp (x : AST.Type.t) = 
    match x with 
    | TpName name_seg -> begin 
      let rest, h = NonEmptyList.unsnoc name_seg in
      assert ((List.length rest) = 0);
      let AST.Type.TpIdSeg {id = id; gen_inst = gen_inst} = h in
      (* assert ((List.length gen_inst) = 0); *)
      (id, gen_inst)
    end
    | TpTup _ -> assert false

  let id_of_tp (x : AST.Type.t) = 
    match x with 
    | TpName name_seg -> begin 
      let rest, h = NonEmptyList.unsnoc name_seg in
      assert ((List.length rest) = 0);
      let AST.Type.TpIdSeg {id = id; gen_inst = gen_inst} = h in
      assert ((List.length gen_inst) = 0);
      id
    end
    | TpTup _ -> assert false

  let tp_of_id (x : id_t) = 
    AST.Type.simple x

  let expr_of_str (x : string) = 
    AST.Prog.NameSeg (x, [])

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
    let h, suffix_list = NonEmptyList.uncons suffix_list in
    let prefix_list = prefix_list @ [h] in
    prefix_list, suffix_list
  
  let expr_lst_to_dot_expr
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
  let dot_expr_to_expr_lst (x : AST.Prog.expr_t) = 
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

  let debug_print (e : string) = 
    Printf.printf "[+] %s \n" (e)
  
  let debug_print_expr (e) = 
    Printf.printf "[+] %s \n" (str_of_expr e)

  let expr_lst_to_and exprs = 
    let rec aux lst = 
      match lst with 
      | [] -> expr_blank
      | l :: rest -> begin
        let r = aux rest in
        match is_expr_blank r with
        | true -> l 
        | false -> Binary (Syntax.Common.And, l, r)
      end in aux exprs

  module Expr = struct 
    type t = AST.Prog.expr_t
    let compare e1 e2 = 
      let e1_str = str_of_expr e1 in
      let e2_str = str_of_expr e2 in 
      if e1_str = e2_str then 0 
      else if e1_str < e2_str then -1 
      else 1
  end ;;

end
