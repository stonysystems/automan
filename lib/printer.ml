(** Pretty printer. *)

open Syntax
open Str
open Internal


let holder (x : string) = 
  Printf.sprintf "[Printer for %s hasn't been implemented.]" x

let debug_print (e : string) = 
  Printf.printf "[+] %s \n" (e)

module CommonPrinter = struct 
  let print_lit (x : Common.lit_t) =
    match x with
    | True      -> "true"
    | False     -> "false"
    | Null      -> "null"
    | Nat d     -> string_of_int d
    | Char d    -> String.make 1 d
    | String d  -> d

  let print_dotsuffix (x : Common.dotsuffix_t) = 
    match x with
    | DSRequires -> "requires"
    | DSReads    -> "reads"
    | DSId id    -> id
    | DSDig i    -> string_of_int i

  let print_quantifier (x : Common.quantifier_t) = 
    match x with
    | Forall -> "forall"
    | Exists -> "exists"

  let print_uop (x : Common.uop_t) = 
    match x with
    | Neg -> "-"
    | Not -> "!"

  let print_bop (x : Common.bop_t) = 
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

  let printopdecl_modifier (x : Common.topdecl_modifier_t) = 
    match x with
    | Abstract  -> "abstract"
    | Ghost     -> "ghost"
    | Static    -> "static"
    | Opaque    -> "opaque"
    ^ " "

  let print_import (x : Common.import_t) =
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

end

module PrettyPrinter (M : MetaData) = struct
  module AST = AST(M)

  let remove_newlines_and_tabs s =
    global_replace (regexp "[\n\t]") "" s

  let get_indt_str n = 
    let rec aux acc n = 
      if n <= 0 then acc
      else aux (acc ^ "\t") (n - 1)
    in
    (aux "" n)

  let get_indt_str_with_new_line n = 
    "\n" ^ (get_indt_str n)

  module Type = struct 
    let rec print_name_seg (x : AST.Type.name_seg_t) = 
      match x with | TpIdSeg tp_id_seg ->
      let (id, gen_inst) = (tp_id_seg.id, tp_id_seg.gen_inst) in
      let gen_inst_str = print_gen_inst gen_inst in
      id ^ gen_inst_str

    and print (x : AST.Type.t) = 
      let aux (x : AST.Type.t list) = 
        let x' = Internal.NonEmptyList.coerce x in
        let (rest, h) = Internal.NonEmptyList.unsnoc x' in
        (print h), rest
      in
      match x with
      | TpName (_, name_seg_t_lst) -> (
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
                List.map print_name_seg name_seg_t_lst in
              String.concat "." name_seg_t_lst_str_lst
            )
      )
      | TpTup t_lst -> (
        let t_lst_str_lst = List.map print t_lst in
        let t_lst_str = String.concat ", " t_lst_str_lst in
        Printf.sprintf "(%s)" t_lst_str
      )

    and print_gen_inst (x : AST.Type.t list) = 
      let x' = List.map print x in
      let x'' = String.concat ", " x' in
      match x'' with
      | "" -> x''
      | _  -> Printf.sprintf "<%s>" x''
  end

  let print_augmented_dotsuffix (x : AST.augmented_dotsuffix_t) = 
    let (x_dotsuffix_t, tp_t_lst) = x in
    (CommonPrinter.print_dotsuffix x_dotsuffix_t) ^ (Type.print_gen_inst tp_t_lst)

  module Prog = struct

    let rec print_name_seg (x : AST.Prog.name_seg_t) = 
      let (id, tp_lst) = x in
      id ^ (Type.print_gen_inst tp_lst)
  
    and print_suffx (x : AST.Prog.suffix_t) = 
      match x with
      | AugDot x -> "." ^ (print_augmented_dotsuffix x)
      | DataUpd (_, x) -> (
        let x = Internal.NonEmptyList.as_list x in
        let x' = List.map print_member_binding_upd x in
        Printf.sprintf ".(%s)" (String.concat ", " x')
      )
      | Subseq x -> (
        let lb, ub = x.lb, x.ub in
        let aux (x : AST.Prog.expr_t option) = 
          match x with
          | None -> ""
          | Some x -> print_expr x 0
        in
        Printf.sprintf "[%s : %s]" (aux lb) (aux ub)
      )
      | SliceLen x -> (
        let sublens, to_end = x.sublens, x.to_end in
        let sublens = Internal.NonEmptyList.as_list sublens in
        let sublens' = List.map print_expr_in_one_line sublens in
        Printf.sprintf "[%s]" (String.concat " : " sublens') ^
          match to_end with
          | true -> ":"
          | false -> ""
      )
      | SeqUpd x -> (
        let idx, v = x.idx, x.v in
        Printf.sprintf "[%s := %s]" 
          (print_expr_in_one_line idx) (print_expr_in_one_line v)  
      )
      | Sel x -> Printf.sprintf "[%s]" (print_expr_in_one_line x)
      | ArgList ({positional = pos ; named = ns}, _) -> (
          let pos' = List.map print_expr_in_one_line pos in
          let ns' = List.map print_named_arg_in_one_line ns in
          Printf.sprintf "(%s)"
            (String.concat ", " (pos' @ ns'))
        )

    and print_pattern (x : AST.Prog.pattern_t) = 
      match x with
      | PatVar (id, tp_option) -> (
          match tp_option with 
          | Some tp -> Printf.sprintf "%s: %s" id (Type.print tp)
          | None -> id
      )
      | PatCtor _ -> holder "Prog.pattern_t.PatCtor"

    and print_expr (x : AST.Prog.expr_t) (idnt_lvl : int) = 
      let idnt_str = (get_indt_str_with_new_line idnt_lvl) in
      idnt_str ^
      match x with
      | Suffixed (x_expr_t, x_suffix_t) -> (
         (print_expr_in_one_line x_expr_t) ^ (print_suffx x_suffix_t)
      )
      | NameSeg x -> print_name_seg x
      | Lambda (inputs, x_expr_t) -> (
        let inputs' = List.map (
          fun h -> 
            let (id, tp_option) = h in
              match tp_option with
              | Some tp -> Printf.sprintf "%s : %s" id (Type.print tp)
              | None -> id
        ) inputs in
        Printf.sprintf "(%s) => %s" 
          (String.concat ", " inputs')
          (print_expr_in_one_line x_expr_t)
      )
      | MapDisplay x_lst -> (
        let x_lst' = List.map (
          fun h ->
            let (e1, e2) = h in
            ((print_expr_in_one_line e1) ^ ": " ^ (print_expr_in_one_line e2))
        ) x_lst in
        Printf.sprintf "map[%s]" (String.concat ", " x_lst')
      )
      | SeqDisplay x -> (
        print_seq_display x
      )
      | SetDisplay x_lst -> (
        let x_lst' = List.map print_expr_in_one_line x_lst in
        Printf.sprintf "{%s}" (String.concat ", " x_lst')
      )
      | If (_, e1, e2, e3) -> (
        Printf.sprintf "if %s then %s %selse %s"
            (print_expr_in_one_line e1)
            (print_expr e2 (idnt_lvl + 1))
            idnt_str
            (print_expr e3 (idnt_lvl + 1))
      )
      | Quantifier (_, x) -> (
        Printf.sprintf "(%s %s :: %s)"
            (CommonPrinter.print_quantifier x.qt)
            (print_qdom x.qdom)
            (print_expr_in_one_line x.qbody)
      )
      | Let x -> (
        Printf.sprintf "var %s%s := %s; %s%s" 
          (
            match x.ghost with
            | true -> "ghost "
            | false -> ""
          )
          (
            let p_lst = Internal.NonEmptyList.as_list x.pats in
            let p_lst' = List.map print_pattern p_lst in
            let str = String.concat ", " p_lst' in
            match List.length p_lst with
            | 1 -> str
            | _ -> "(" ^ str ^ ")"
          )
          (
            let defs_lst = Internal.NonEmptyList.as_list x.defs in
            let defs_lst' = List.map print_expr_in_one_line defs_lst in
            String.concat ", " defs_lst'
          )
          (get_indt_str idnt_lvl)
          (print_expr x.body idnt_lvl)
      )
      | Lit x -> CommonPrinter.print_lit x 
      | Cardinality x -> Printf.sprintf "|%s|" (print_expr_in_one_line x)
      | Binary (_, bop, expr_l, expr_r) -> (
        let get_bop_priority (bop : Common.bop_t) = 
          match bop with
          | Mul | Div | Mod -> 1
          | Add | Sub -> 2
          | Lt | Lte | Gt | Gte -> 3
          | Eq | Neq -> 4
          | In | Nin | Disjoint -> 5 (* Not sure *)
          | And -> 6
          | Or -> 7
          | Implies | Equiv -> 8
        in
        let get_expr_priority (x : AST.Prog.expr_t) = 
          match x with
          | Binary (_, bop, _, _) -> get_bop_priority bop
          | _ -> 0
        in
        let aux expr printer = 
          let expr_str = printer expr in
          match (get_expr_priority expr) > (get_bop_priority bop) with
          | true -> Printf.sprintf "(%s)" expr_str
          | false -> expr_str
        in
        Printf.sprintf "%s %s%s %s"
        (aux expr_l print_expr_in_one_line)
        ( 
          match bop with
          | And -> idnt_str
          | _ -> ""
        )
        (CommonPrinter.print_bop bop)
        (
          match bop with 
          | And -> (aux expr_r (fun x -> print_expr x idnt_lvl))
          | _ -> print_expr_in_one_line expr_r
        )
      )
      | Tuple (exprs) -> begin
        Printf.sprintf "(%s)" 
          begin 
            let exprs' = List.map print_expr_in_one_line exprs in 
            String.concat ", " exprs'
          end
      end
      | _ -> holder "..."

    and print_expr_in_one_line (x) = 
      let res = print_expr x 0 in
      remove_newlines_and_tabs res

    and print_named_arg_in_one_line (narg : (id_t * AST.Prog.expr_t)) =
      let (id, e) = narg in
      let e' = print_expr_in_one_line e in
      id ^ " := " ^ e'

    and print_member_binding_upd (x : AST.Prog.member_binding_upd_t) = 
      let (either_t, x_expr_t) = x in
      (
        match either_t with
        | Left id -> id 
        | Right i -> string_of_int i
      )
      ^ " := " ^ (print_expr_in_one_line x_expr_t)

    and print_seq_display (x : AST.Prog.seq_display_t) = 
      match x with
      | SeqEnumerate input -> (
        let input' = List.map print_expr_in_one_line input in
        Printf.sprintf "[%s]" (String.concat ", " input')
      )
      | SeqTabulate input -> (
        let gen_inst, len, func = input.gen_inst, input.len, input.func in
        Printf.sprintf "seq%s(%s, %s)" 
          (Type.print_gen_inst gen_inst)
          (print_expr_in_one_line len)
          (print_expr_in_one_line func)
      )

    and print_attribute (x : AST.Prog.attribute_t) = 
      let id, markers = x in
      let markers' = List.map print_expr_in_one_line markers in
      Printf.sprintf "{:%s %s}" id (String.concat ", " markers')

    and print_attributes (x : AST.Prog.attribute_t list) = 
      let x' = List.map print_attribute x in
      String.concat "" x'

    and print_qvar_decl (x : AST.Prog.qvar_decl_t) = 
      match x with QVar (id, tp_o, cdom, attrs) ->
        Printf.sprintf "%s%s%s"
        (
          id ^
          match tp_o with
          | Some tp -> Printf.sprintf ": %s" (Type.print tp)
          | None -> ""
        )
        (
          match cdom with
          | Some e -> Printf.sprintf " <- %s" (print_expr_in_one_line e)
          | None -> ""
        )
        (print_attributes attrs)

    and print_qdom (x : AST.Prog.qdom_t) = 
      match x with QDom x ->
      Printf.sprintf "%s%s"
      (
        let qvars' = List.map print_qvar_decl x.qvars in
        String.concat ", " qvars'
      )
      (
        match x.qrange with 
        | Some e -> " | " ^ (print_expr_in_one_line e)
        | None -> ""
      )

    and print_lhs (x : AST.Prog.lhs_t) = 
      print_expr_in_one_line x

  end

  module TopDecl = struct
    let print_formal (x : AST.TopDecl.formal_t) =
      match x with Formal (ghost, id, tp) ->
      Printf.sprintf "%s%s: %s"
        (if ghost then "ghost " else "")
        id (Type.print tp)

    let print_formals (x : AST.TopDecl.formal_t list) =
      let x' = List.map print_formal x in 
      Printf.sprintf "(%s)" (String.concat ", " x')

    let print_datatype_ctor 
      (x : AST.TopDecl.datatype_ctor_t) (idnt_lvl : int) = 
      let idnt_str = get_indt_str_with_new_line idnt_lvl in
      match x with DataCtor (attrs, id, fmls) ->
        let _ = fmls in
        Printf.sprintf "%s%s%s"
        id
        (Prog.print_attributes attrs)
        (
          Printf.sprintf "(%s%s%s)"
            idnt_str
            (
              let fmls' = List.map print_formal fmls in 
              String.concat (", " ^ idnt_str) fmls'
            )
            (get_indt_str_with_new_line (idnt_lvl - 1))
        )

    let print_datatype 
      (x : AST.TopDecl.datatype_t) (idnt_lvl : int) = 
      let idnt_str = get_indt_str_with_new_line idnt_lvl in
      let _, attrs, id, gen_params, ctors = x in
      let ctors = NonEmptyList.as_list ctors in
      let _ = gen_params in (* How to print gen_params ? *)
      Printf.sprintf "datatype %s%s = %s%s"
        id
        (Prog.print_attributes attrs)
        idnt_str
        (
          let ctors' = 
            List.map (fun x -> print_datatype_ctor x (idnt_lvl + 1)) ctors in
          String.concat (idnt_str ^ " | " ^ idnt_str) ctors'
        )

    let print_function_spec 
      (x : AST.TopDecl.function_spec_t) (idnt_lvl : int) = 
      let idnt_str = (get_indt_str_with_new_line idnt_lvl) in
      idnt_str ^
      match x with
      | Requires e -> Printf.sprintf "%s %s" "requires" (Prog.print_expr_in_one_line e)
      | Reads e -> Printf.sprintf "%s %s" "reads" (Prog.print_expr_in_one_line e)
      | Ensures e -> Printf.sprintf "%s %s" "ensures" (Prog.print_expr_in_one_line e)
      | Decreases e -> Printf.sprintf "%s %s" "decreases" (Prog.print_expr_in_one_line e)

    let print_function (x : AST.TopDecl.function_t) (idnt_lvl : int) = 
      let idnt_str = (get_indt_str_with_new_line idnt_lvl) in
      match x with
      | Predicate (_, _, _, p, _, fs, specs, e) -> (
        let fs' = List.map print_formal fs in
        let fs_str = String.concat ", " fs' in
        let specs' = List.map 
          (fun x -> print_function_spec x (idnt_lvl + 1)) specs in 
        let specs_str = String.concat "" specs' in
        Printf.sprintf 
          "\n%spredicate %s(%s) %s%s{%s%s}" 
            idnt_str p fs_str 
            specs_str
            idnt_str (Prog.print_expr e (idnt_lvl+1)) idnt_str
      )
      | Function (is_fm, _, id, [], fs, rtn_tp, specs, e) -> (
        let fs' = List.map print_formal fs in
        let fs_str = String.concat ", " fs' in
        let specs' = List.map 
          (fun x -> print_function_spec x (idnt_lvl + 1)) specs in 
        let specs_str = String.concat "" specs' in
        Printf.sprintf 
          "\n%s%s %s(%s) : %s %s%s{%s%s}" 
            idnt_str 
            (match is_fm with | true -> "function method" | false -> "function") 
            id fs_str (Type.print rtn_tp)
            specs_str
            idnt_str (Prog.print_expr e (idnt_lvl+1)) idnt_str
      )
      | _ -> ""

    let rec print' (x : AST.TopDecl.t') (idnt_lvl : int) = 
      let idnt_str = (get_indt_str_with_new_line idnt_lvl) in
      match x with
      | ModuleImport i -> idnt_str ^ (CommonPrinter.print_import i)
      | ModuleDef d -> idnt_str ^ (print_module_def d idnt_lvl)
      | DatatypeDecl d -> "\n" ^ idnt_str ^ (print_datatype d idnt_lvl)
      | PredFunDecl x -> print_function x idnt_lvl
      | _ -> "\n" ^ idnt_str ^ "[ Hasn't been implemented in Printer yet ]"
    
    and print (x : AST.TopDecl.t) (idnt_lvl : int) = 
      let (m, t') = x in
      let m' = List.map CommonPrinter.printopdecl_modifier m in
        Printf.sprintf "%s%s"
        (String.concat "" m') (print' t' idnt_lvl)

    and print_module_def 
      (x : AST.TopDecl.module_def_t) (idnt_lvl : int) = 
      let (attrs, id, t_lst) = x in
      let t_lst' = List.map (fun x -> print x (idnt_lvl + 1)) t_lst in
      Printf.sprintf "\nmodule%s %s \n{%s\n}" 
        (Prog.print_attributes attrs) id (String.concat "" t_lst')
  end

  let print (x : AST.t) = 
    match x with Dafny x ->
      let includes, decls  = x.includes, x.decls in
      let includes' = List.map (
        fun h ->
          Printf.sprintf "include \"%s\"" h
      ) includes in
      let decls' = List.map (
        fun h ->
          TopDecl.print h 0
      ) decls in
      Printf.sprintf "%s\n%s" 
        (String.concat "\n" includes')
        (String.concat "\n" decls')

end


