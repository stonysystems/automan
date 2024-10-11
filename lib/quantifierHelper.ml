open Syntax
open Internal

module AST = AST(Moder.ModingMetaData)
module TCommon = TranslatorCommon.TranslatorCommon
module Printer = Printer.PrettyPrinter (Moder.ModingMetaData)


module QuantifierHelper = struct 

  (**
    * Describe the domain of a seq 
    * |collection_name| == len 
    *)
  type seq_dom = { collection_name : AST.Prog.expr_t; len : AST.Prog.expr_t }

  (**
    * Describe the mapping of a seq/map
    * seq : i :: 0 <= i < |collection_name| ==> collection_name[i] == value 
    * map : forall opn :: opn in votes' ==> votes'[opn] == votes[opn]
    *)
  type col_map = { 
    i : string;
    collection_name : AST.Prog.expr_t; 
    value : AST.Prog.expr_t }

  (**
    * (forall opn :: opn in votes' <==> opn in votes && opn >= log_truncation_point)
    * The binary operation must be "Syntax.Common.Equiv"  
    * The left operation must be "opn in votes'"
    *)
  type map_dom = {
    (* opn, Syntax.AST.Prog.QDom.qvar *)
    i : string ; 
    (* votes', from Moder.Definitions.QFVarDom *)
    collection_name : AST.Prog.expr_t ; 
    (* opn in votes && opn >= log_truncation_point *)
    dom : AST.Prog.expr_t ;
  }

  (**
    * Manage the doms and maps visited so far
    *)
  type quantifier_booker = 
  {
    seq_doms : seq_dom list ;
    seq_maps : col_map list ;
    map_doms : map_dom list ;
    map_maps : col_map list ;
  }

  let str_of_expr (x : AST.Prog.expr_t) : string = 
    Printer.Prog.print_expr_in_one_line x
  
  let is_two_expr_eq x y = 
    (str_of_expr x) = (str_of_expr y)

  let is_seq_dom_and_map_match
    (dom : seq_dom)
    (map : col_map) : bool = 
    (is_two_expr_eq dom.collection_name map.collection_name)

  let is_map_dom_and_map_match
    (dom : map_dom)
    (map : col_map) : bool = 
    (is_two_expr_eq dom.collection_name map.collection_name)

  let construct_seq_display 
    (booker : quantifier_booker) 
    : (AST.Prog.seq_display_t * AST.Prog.expr_t) option = 
    let aux (map : col_map) : 
      (AST.Prog.seq_display_t * AST.Prog.expr_t) option = 
      let rec aux lst = 
        match lst with 
        | [] -> None
        | h :: rest -> 
          (match (is_seq_dom_and_map_match h map) with
          | false -> aux rest
          | true -> 
            (* Printf.printf "!!! %s\n" (str_of_expr map.collection_name); *)
            Some 
            (AST.Prog.SeqTabulate 
              {gen_inst = [] ; 
              len = h.len ; 
              func = 
                AST.Prog.Lambda 
                  ([(map.i, None)], map.value)}, 
                    map.collection_name))
      in
      aux booker.seq_doms
    in
    match booker.seq_maps with 
    | [] -> None
    | h :: _ -> aux h

  let construct_map_qtf
    (booker : quantifier_booker)
    : (AST.Prog.map_comp_t * AST.Prog.expr_t) option = 
    let aux (map : col_map) :
      (AST.Prog.map_comp_t * AST.Prog.expr_t) option = 
      let rec aux lst = 
        match lst with 
        | [] -> None
        | h :: rest -> 
          (match (is_map_dom_and_map_match h map) with
          | false -> aux rest 
          | true ->  
            (let domain = h.dom in
              (* Printf.printf "%s" (str_of_expr domain); *)
              Some 
              (
                let comp : AST.Prog.map_comp_t = 
                {
                  imap = false ;
                  qdom = AST.Prog.QDom 
                  {
                    qvars = [AST.Prog.QVar (map.i, None, None, [])] ; 
                    qrange = Some domain ; 
                  };
                  key = None ;
                  valu = map.value ;
                } in comp
                (* AST.Prog.Quantifier (
                None, 
                {qt = Common.Forall ; 
                  qdom = AST.Prog.QDom 
                    {
                      qvars = [AST.Prog.QVar (map.i, None, None, [])] ; 
                      qrange = Some (domain) ; 
                    };
                  qbody = map.value;
                }) *)
                , map.collection_name)))
      in aux booker.map_doms
    in
    match booker.map_maps with 
    | [] -> None 
    | h :: _ -> aux h

  let print_seq_doms (booker : quantifier_booker) : unit = 
    let print_seq_dom (x : seq_dom) : unit = 
      Printf.printf "[+] |%s| == %s \n" 
        (Printer.Prog.print_expr_in_one_line x.collection_name)
        (Printer.Prog.print_expr_in_one_line x.len)
    in
    let _ = List.map print_seq_dom booker.seq_doms in
    ()

  let print_col_maps (booker : quantifier_booker) : unit = 
    let print_col_map (x : col_map) : unit = 
      Printf.printf "[+] 0 <= %s < |%s| ==> %s[%s] == %s \n" 
        x.i 
        (Printer.Prog.print_expr_in_one_line x.collection_name)
        (Printer.Prog.print_expr_in_one_line x.collection_name)
        x.i
        (Printer.Prog.print_expr_in_one_line x.value)
    in
    let _ = List.map print_col_map booker.seq_maps in
    ()

  let init = {
    seq_doms = [] ; 
    seq_maps = [] ;
    map_doms = [] ;
    map_maps = [] ;
  }

  let get_the_right_expr_from_a_eq (eq : AST.Prog.expr_t) : AST.Prog.expr_t = 
    match eq with 
    | Binary (_, bop, _, re) ->
      (match bop with 
        | Eq -> re
        | _ -> assert false)
    | _ -> assert false


  let expr_of_str (x : string) = 
    AST.Prog.NameSeg (x, [])

  let expr_lst_to_dot_expr
  (lst : AST.Prog.expr_t list) : AST.Prog.expr_t = 
    let expr_to_id (e : AST.Prog.expr_t) : id_t = 
      match e with 
      | NameSeg name_seg -> begin
        let id, _ = name_seg in id
      end
      | _ -> assert false
    in
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
  
  (**
    * [BUG] : 
    *   `a.last_checkpointed_operation[idx] == 0`
    *    is parsing as 
    *   `a.last_checkpointed_operation[idx] == 0 && true`
    *)
  let erase_unecessary_and_conj
    (e : AST.Prog.expr_t) : AST.Prog.expr_t = 
    match e with 
    | Binary (_, bop, e1, e2) -> (
      match bop with 
      | And -> 
        (match (Printer.Prog.print_expr_in_one_line e2) with
        | "true" -> e1 | _ -> e) 
      | _ -> e
    )
    | _ -> e

  (**
    * For each trier, it returns a tuple with 
    * 1. bool : whether this expression matches a template and 
    *           has been added to the booker.
    * 2. booker : the booker, either unmodified or updated.
    *)

  (**
    * forall idx | 0 <= idx < |s| :: s[idx] == \<expr\>
    *)
  let try_add_seq_dom 
    (e : AST.Prog.expr_t) 
    (booker : quantifier_booker) : 
    (bool * quantifier_booker) = 
    match e with 
    | Binary (meta, _, le, re) -> (
      match meta with 
      | Some (meta : Moder.Definitions.binary_op_functionalize_t) -> (
        match meta with 
        | Moder.Definitions.Eq meta -> (
          let (le, re) = 
            match meta.outvar_is_left with 
            | true -> (le, re) | false -> (re, le)
          in
          match le with 
          | AST.Prog.Cardinality collection_name -> 
            (
              true, 
              { booker with seq_doms = (
                  booker.seq_doms @ [{
                  collection_name = collection_name; len = re 
                }]
              )}
            )
          | _ -> (false, booker)
        )
        | Moder.Definitions.And _ -> (false, booker)
      )
      | None -> (false, booker)
    )
    | _ -> (false, booker)
  
  let try_add_seq_map 
    (e : AST.Prog.expr_t) 
    (booker : quantifier_booker)
    : (bool * quantifier_booker) = 
    match e with 
    | AST.Prog.Quantifier (meta, quantifier) -> 
      (
        match meta with 
        | Some meta -> (
          let qvar = meta.qvar in 
          match qvar with 
          | Moder.Definitions.QFVarRange var_range -> 
            let (range_sort, outvar) = var_range.domain in 
            (
              match range_sort with 
              | Moder.Definitions.QFVarRangeBounds ->
                let q_body = quantifier.qbody in 
                let q_body = erase_unecessary_and_conj q_body in
                let collection_name = 
                  NonEmptyList.as_list outvar.mq_outvar in
                let collection_name = 
                  expr_lst_to_dot_expr
                    (List.map expr_of_str collection_name) in
                let value = get_the_right_expr_from_a_eq q_body in
                let i = var_range.id in
                ( true, 
                  { booker with seq_maps = (
                    [{
                        i = i;
                        collection_name = collection_name; 
                        value = value 
                      }] @ booker.seq_maps
                  ) })
              | Moder.Definitions.QFVarRangeColl -> (false, booker)
            )
          | Moder.Definitions.QFVarDom _ -> (false, booker)
        )
        | None -> (false, booker)
      )
    | _ -> (false, booker)

  let expr_of_outvar (outvar : Moder.Definitions.outvar_lhs_t) = 
    let expr_lst = 
      List.map expr_of_str (NonEmptyList.as_list outvar.mq_outvar) in
    expr_lst_to_dot_expr expr_lst

  let try_add_map_dom 
    (e : AST.Prog.expr_t) 
    (booker : quantifier_booker)
    : (bool * quantifier_booker) = 
    let basic = (false, booker) in
    match e with 
    | AST.Prog.Quantifier (meta, quantifier) ->
      (
        match meta with 
        | Some meta -> (
          match meta.qvar with 
          | Moder.Definitions.QFVarRange _ -> basic
          | Moder.Definitions.QFVarDom outvar ->
            let collection_name = expr_of_outvar outvar in
            (* Printf.printf "%s\n" (str_of_expr collection_name) ; *)
            let qdom = quantifier.qdom in
            match qdom with AST.Prog.QDom qdom ->
            match qdom.qvars with 
            | [] -> basic
            | h :: _ ->
              match h with AST.Prog.QVar (i, _, _, _) ->
              (* Printf.printf ("%s\n") i ; *)
              match quantifier.qbody with 
              | AST.Prog.Binary (_, bop, e1, e2) ->
                (
                  match bop with 
                  | Common.Equiv -> (
                    let should_match = 
                      AST.Prog.Binary
                      (None, Common.In, (expr_of_str i), collection_name) in
                    (* Printf.printf "%s\n" (str_of_expr should_match) ; *)
                    match (is_two_expr_eq should_match e1) with 
                    | true -> (
                      let map_dom = {
                        i = i ; collection_name = collection_name ; dom = e2 ;
                      } in
                      ( true, 
                      { booker with map_doms = (
                        map_dom :: booker.map_doms
                      ) })
                    )
                    | false -> basic
                  )
                  | _ -> basic
                )
              | _ -> basic
        )
        | None -> basic
      )
    | _ -> basic
  
    let try_add_map_map 
      (e : AST.Prog.expr_t) 
      (booker : quantifier_booker)
      : (bool * quantifier_booker) = 
      let basic = (false, booker) in
      match e with 
      | AST.Prog.Quantifier (meta, quantification) ->
        (
          match meta with 
          | None -> basic
          | Some meta ->
            match meta.qvar with 
            | Moder.Definitions.QFVarDom _ -> basic
            | Moder.Definitions.QFVarRange var_range ->
              let i = var_range.id in
              (* Printf.printf "%s\n" i ; *)
              let (range_sort, outvar) = var_range.domain in
              match range_sort with 
              | Moder.Definitions.QFVarRangeBounds -> basic
              | Moder.Definitions.QFVarRangeColl ->
                let collection_name = expr_of_outvar outvar in
                (* Printf.printf "%s\n" (str_of_expr collection_name) ; *)
                match meta.body_outvars with
                | [] -> basic
                | out_var :: _ -> 
                  let coll_in_out_var = expr_of_outvar out_var in
                  match out_var.fieldlike with 
                  | None -> basic
                  | Some feildlike ->
                    match feildlike with 
                    | Moder.Definitions.Cardinality -> basic
                    | Moder.Definitions.Sel i' ->
                      match 
                        (i = i') && 
                        (is_two_expr_eq coll_in_out_var collection_name) with
                      | false -> basic
                      | true -> 
                        let q_body = quantification.qbody in
                        let q_body = erase_unecessary_and_conj q_body in
                        match q_body with 
                        | Binary (meta, _bop, e1, e2) ->
                          (
                            match meta with
                            | None -> basic
                            | Some meta -> 
                              match meta with 
                              | Moder.Definitions.And _ -> basic
                              | Moder.Definitions.Eq eq -> 
                                let value = (
                                  match eq.outvar_is_left with 
                                  | true -> e2 
                                  | false -> e1
                                ) in
                                (* Printf.printf "%s\n" (str_of_expr value) ; *)
                                let map_map = {
                                  i = i ; 
                                  collection_name = collection_name ; 
                                  value = value ;
                                } in
                                ( true, 
                                { booker with map_maps = (
                                  map_map :: booker.map_maps
                                ) })
                          )
                        | _ -> basic

        )
      | _ -> basic

end
