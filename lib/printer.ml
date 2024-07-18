(** Pretty printer. *)

open Syntax
open Str
open Internal

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
      let gen_inst_str_lst = List.map print_t gen_inst in
      let gen_inst_str = String.concat "," gen_inst_str_lst in
      Printf.sprintf "%s<%s>" id gen_inst_str

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
  end

  module ModuleItem = struct
  let print_t (x : ParserPass.ModuleItem.t) (idnt_lvl : int) = 
    let idnt_str = (get_indt_str idnt_lvl) in
    match x with
    | Import i -> (
      let op_str = 
        match i.opened with 
        | true -> "opened "
        | false -> ""
      in
      let tgt_str = 
        NonEmptyList.fold_left_1 (fun x y -> x ^ "." ^ y) i.tgt in
      match i.mref with
      | Some (m_rf_t, rf_str) -> (
        let marker = 
          match m_rf_t with
          | Concrete -> "="
          | Abstract -> ":"
        in
          Printf.sprintf 
            "%simport %s%s%s%s" idnt_str rf_str marker op_str tgt_str
      )
      | None -> Printf.sprintf "%simport %s%s" idnt_str op_str tgt_str
    )
    | Predicate (p, fs, specs, e) -> (
      let _ = fs in
      let _ = specs in 
      let _ = e in
      Printf.sprintf 
        "\n%spredicate %s() %s{%s}" 
          idnt_str p idnt_str idnt_str
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
