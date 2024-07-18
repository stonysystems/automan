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

  (* let type_t x = 
    "" *)

  let module_item (x : ParserPass.ModuleItem.t) (idnt_lvl : int) = 
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
          Printf.sprintf "%simport %s%s%s%s" idnt_str rf_str marker op_str tgt_str
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

  let file_level (x : ParserPass.FileLevel.t) = 
    match x with
    | Include fp -> Printf.sprintf "include \"%s\"" fp
    | Module (m, ds) -> (
      let ds_str_lst = List.map (fun x -> module_item x 1) ds in
      let ds_str = String.concat "" ds_str_lst in
      Printf.sprintf "\nmodule %s \n{%s\n}" m ds_str
    )
end
