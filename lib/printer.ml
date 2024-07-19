(** Pretty printer. *)

open Syntax
open Str
open Internal


let print_dotsuffix_t (x : dotsuffix_t) = 
  match x with
  | DSRequires -> "requires"
  | DSReads    -> "reads"
  | DSId id    -> id
  | DSDig i    -> string_of_int i

module PrettyPrinter = struct
  let remove_newlines_and_tabs s =
    global_replace (regexp "[\n\t]") "" s

  let get_indt_str n = 
    let rec aux acc n = 
      if n <= 0 then acc
      else aux (acc ^ "\t") (n - 1)
    in
    "\n" ^ (aux "" n)

  module Type = struct 
    let rec print_name_seg_t (x : ParserPass.Type.name_seg_t) = 
      match x with | TpIdSeg tp_id_seg ->
      let (id, gen_inst) = (tp_id_seg.id, tp_id_seg.gen_inst) in
      let gen_inst_str = print_and_join_t gen_inst in
      id ^ gen_inst_str

    and print_t (x : ParserPass.Type.t) = 
      let aux (x : ParserPass.Type.t list) = 
        let x' = Internal.NonEmptyList.coerce x in
        let (rest, h) = Internal.NonEmptyList.unsnoc x' in
        (print_t h), rest
      in
      match x with
      | TpName (name_seg_t_lst) -> (
          let (_, h) = Internal.NonEmptyList.unsnoc name_seg_t_lst in
          match h with | TpIdSeg tp_id_seg ->
            let (id, gen_inst) = (tp_id_seg.id, tp_id_seg.gen_inst) in
            match id with
            | "int" | "bool" | "nat" | "string" -> id
            | "seq" | "set" -> (
              let elem_str, _ = aux gen_inst in
              Printf.sprintf "%s<%s>" id elem_str
            )
            | "map" -> (
              let k_str, rest = aux gen_inst in
              let v_str, _ = aux rest in
              Printf.sprintf "%s<%s, %s>" id k_str v_str
            )
            | _ -> (
              let name_seg_t_lst = 
                Internal.NonEmptyList.as_list name_seg_t_lst in
              let name_seg_t_lst_str_lst = 
                List.map print_name_seg_t name_seg_t_lst in
              String.concat "." name_seg_t_lst_str_lst
            )
      )
      | TpTup t_lst -> (
        let t_lst_str_lst = List.map print_t t_lst in
        let t_lst_str = String.concat "" t_lst_str_lst in
        Printf.sprintf "(%s)" t_lst_str
      )

    and print_and_join_t (x : ParserPass.Type.t list) = 
      let x' = List.map print_t x in
      let x'' = String.concat ", " x' in
      match x'' with
      | "" -> x''
      | _  -> Printf.sprintf "<%s>" x''
  end

  let print_augmented_dotsuffix_t (x : ParserPass.augmented_dotsuffix_t) = 
    let (x_dotsuffix_t, tp_t_lst) = x in
    (print_dotsuffix_t x_dotsuffix_t) ^ (Type.print_and_join_t tp_t_lst)

  module Prog = struct
    let print_lit_t (x : ParserPass.Prog.lit_t) =
      match x with
      | True      -> "true"
      | False     -> "false"
      | Null      -> "null"
      | Nat d     -> string_of_int d
      | Char d    -> String.make 1 d
      | String d  -> d

    let print_quantifier_t (x : ParserPass.Prog.quantifier_t) = 
      match x with
      | Forall -> "forall"
      | Exists -> "exists"

    let print_uop_t (x : ParserPass.Prog.uop_t) = 
      match x with
      | Neg -> "-"
      | Not -> "!"

    let print_bop_t (x : ParserPass.Prog.bop_t) = 
      match x with 
      | Mul       ->  "*"
      | Div       ->  "/"
      | Mod       ->  "%"
      | Add       ->  "+"
      | Sub       ->  "-"
      | Eq        ->  "=="
      | Neq       ->  "!="
      | Lt        ->  "<"
      | Gt        ->  ">"
      | Lte       ->  "<="
      | Gte       ->  ">="
      | In        ->  "in"
      | Nin       ->  "!in"
      | Disjoint  ->  "!!"
      | And       ->  "&&"
      | Or        ->  "||"
      | Implies   ->  "==>"
      | Equiv     ->  "<==>"
      
    let rec print_name_seg_t (x : ParserPass.Prog.name_seg_t) = 
      let (id, tp_lst) = x in
      id ^ (Type.print_and_join_t tp_lst)
  
    and print_suffx_t (x : ParserPass.Prog.suffix_t) = 
      match x with
      | AugDot x -> "." ^ (print_augmented_dotsuffix_t x)
      | DataUpd x -> (
        let x = Internal.NonEmptyList.as_list x in
        let x' = List.map print_member_binding_upd_t x in
        Printf.sprintf ".(%s)" (String.concat ", " x')
      )
      | Subseq x -> (
        let lb, ub = x.lb, x.ub in
        let aux (x : ParserPass.Prog.expr_t option) = 
          match x with
          | None -> ""
          | Some x -> print_expr_t x 0
        in
        Printf.sprintf "[%s : %s]" (aux lb) (aux ub)
      )
      | SliceLen x -> (
        let sublens, to_end = x.sublens, x.to_end in
        let sublens = Internal.NonEmptyList.as_list sublens in
        let sublens' = List.map print_expr_t_wrapper sublens in
        let sublens'' = String.concat " : " sublens' in
        Printf.sprintf "[%s]" sublens'' ^
          match to_end with
          | true -> ":"
          | false -> ""
      )
      | SeqUpd x -> (
        let idx, v = x.idx, x.v in
        Printf.sprintf "[%s := %s]" 
          (print_expr_t_wrapper idx) (print_expr_t_wrapper v)  
      )
      | Sel x -> Printf.sprintf "[%s]" (print_expr_t_wrapper x)
      | ArgList x -> (
        let x' = List.map print_expr_t_wrapper x in
        Printf.sprintf "(%s)" (String.concat ", " x')
      )

    and print_expr_t (x : ParserPass.Prog.expr_t) (idnt_lvl : int) = 
      let idnt_str = (get_indt_str idnt_lvl) in
      match x with
      | Suffixed (x_expr_t, x_suffix_t) -> (
        idnt_str ^ (print_expr_t x_expr_t 0) ^ (print_suffx_t x_suffix_t)
      )
      | _ -> ""

    and print_member_binding_upd_t (x : ParserPass.Prog.member_binding_upd_t) = 
      let (either_t, x_expr_t) = x in
      match either_t with
      | Left id -> id 
      | Right i -> string_of_int i
      ^ " := " ^ (print_expr_t x_expr_t 0)

    and print_expr_t_wrapper x = 
      print_expr_t x 0
  end

  module ModuleItem = struct

  let print_import_t (x : ParserPass.ModuleItem.import_t) =
    let op_str = 
      match x.opened with 
      | true  -> "opened "
      | false -> ""
    in
    let tgt_str = 
      NonEmptyList.fold_left_1 (fun x y -> x ^ "." ^ y) x.tgt in
    match x.mref with
    | Some (m_rf_t, rf_str) -> (
      let marker = 
        match m_rf_t with
        | Concrete -> "="
        | Abstract -> ":"
      in
        Printf.sprintf 
          "import %s%s%s%s" rf_str marker op_str tgt_str
    )
    | None -> Printf.sprintf "import %s%s" op_str tgt_str

  let print_formal_t (x : ParserPass.ModuleItem.formal_t) =
    match x with Formal (id, tp) ->
    Printf.sprintf "%s : %s" id (Type.print_t tp)

  let print_t (x : ParserPass.ModuleItem.t) (idnt_lvl : int) = 
    let idnt_str = (get_indt_str idnt_lvl) in
    match x with
    | Import i -> idnt_str ^ (print_import_t i)
    | Predicate (p, fs, specs, e) -> (
      let fs_str_lst = List.map print_formal_t fs in
      let fs_str = String.concat ", " fs_str_lst in
      let _ = specs in 
      let _ = e in
      Printf.sprintf 
        "\n%spredicate %s(%s) %s{%s}" 
          idnt_str p fs_str idnt_str idnt_str
    )
    | _ -> "\n" ^ idnt_str ^ "[ Hasn't been implemented in Printer yet ]"
  end

  module FileLevel = struct
  let print_t (x : ParserPass.FileLevel.t) = 
    match x with
    | Include fp -> Printf.sprintf "include \"%s\"" fp
    | Module (m, ds) -> (
      let ds_str_lst = List.map (fun x -> ModuleItem.print_t x 1) ds in
      let ds_str = String.concat "" ds_str_lst in
      Printf.sprintf "\nmodule %s \n{%s\n}" m ds_str
    )
  end
end
