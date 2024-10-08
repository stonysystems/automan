open Syntax
open Internal

module AST = AST(Moder.ModingMetaData)
module TCommon = TranslatorCommon.TranslatorCommon

module QuantifierHelper = struct 

  (* |collection_name| == len *)
  type seq_dom = { collection_name : AST.Prog.expr_t; len : AST.Prog.expr_t }

  (* i :: 0 <= i < |collection_name| ==> collection_name[i] == value *)
  type seq_map = { 
    i : string;
    collection_name : AST.Prog.expr_t; 
    value : AST.Prog.expr_t }

  type quantifier_booker = 
  {
    seq_doms : seq_dom list ;
    seq_maps : seq_map list ;
  }

  let get_the_right_expr_from_a_eq (eq : AST.Prog.expr_t) : AST.Prog.expr_t = 
    match eq with 
    | Binary (_, bop, _, re) ->
      (
        match bop with 
        | Eq -> re
        | _ -> assert false
      )
    | _ -> assert false

  (* let seq_try_apply_dom_and_map 
    (dom : seq_dom)
    (map : seq_map) =  *)

  let try_add_seq_dom 
    (e : AST.Prog.expr_t) 
    (booker : quantifier_booker)
    : (bool * quantifier_booker) = 
    match e with 
    | Binary (meta, _, le, re) -> (
      match meta with 
      | Some (meta : Moder.Definitions.binary_op_functionalize_t) -> (
        match meta with 
        | Moder.Definitions.Eq meta -> (
          let (le, re) = 
            match meta.outvar_is_left with 
            | true -> (le, re)
            | false -> (re, le)
          in
          match le with 
          | AST.Prog.Cardinality collection_name -> (
            (
              true, 
              { booker with seq_doms = (
                  booker.seq_doms @ [{
                  collection_name = collection_name; len = re 
                }]
              )}
            )
          )
          | _ -> assert false
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
                let (id, _) = NonEmptyList.uncons outvar.mq_outvar in
                let collection_name = AST.Prog.NameSeg (id, []) in
                let value = get_the_right_expr_from_a_eq q_body in
                let i = var_range.id in
                (
                  true, 
                  { booker with seq_maps = (
                    booker.seq_maps @ [{
                        i = i;
                        collection_name = collection_name; 
                        value = value 
                      }]
                  ) }
                )
              | Moder.Definitions.QFVarRangeColl -> (false, booker)
            )
          | Moder.Definitions.QFVarDom _ -> (false, booker)
        )
        | None -> (false, booker)
      )
    | _ -> (false, booker)

end
