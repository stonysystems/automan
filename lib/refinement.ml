open Syntax
open Internal


module AST = AnnotationPass
module TCommon = TranslatorCommon.TranslatorCommon

module Refinement  = struct
  let remapper = new NameRemapper.name_remapper

  let s_id = "s"
  let s = TCommon.expr_of_str s_id

  let i_id = "i"
  let i = TCommon.expr_of_str i_id

  let is_valid_token = "IsValid"

  let generate_token t_id token = 
    TCommon.expr_of_str (Printf.sprintf "%s%s" t_id token)

  let is_valid_template t_id = 
    generate_token t_id is_valid_token

  let rec generate_is_valid_4_fmls 
    (fmls : AST.TopDecl.formal_t list) = 
    match fmls with 
    | [] -> []
    | h :: rest -> begin
      match h with AST.TopDecl.Formal (fml_id, fml_tp) ->
      match fml_tp with 
      | TpTup _ -> assert false
      | TpName name_seg_lst -> begin
        let name_seg, _ = NonEmptyList.uncons name_seg_lst in
        let TpIdSeg {id = t_id; gen_inst = gen_inst} = name_seg in
        (
          match List.length gen_inst with 
          | 0 -> begin 
            [AST.Prog.Suffixed (
              is_valid_template t_id, 
              let e = 
                TCommon.expr_lst_to_dot_expr 
                [s; TCommon.expr_of_str fml_id] in
                AST.Prog.ArgList (([e], None))
              )
            ]
          end
          | 1 -> begin (* id is set/seq or an alias to them *)
            let _, param_tp = List.unsnoc gen_inst in
            let param_tp_id = TCommon.id_of_tp param_tp in
            match TCommon.is_primitive param_tp_id with 
            | true -> []
            | false -> [
              Quantifier {
                qt = Syntax.Common.Forall;
                qdom = QDom {
                  qvars = [QVar (i_id, None, None, [])];
                  qrange = None
                };
                qbody = Binary (
                  Syntax.Common.Implies,
                  (AST.Prog.Binary (
                    Syntax.Common.In, 
                    i, 
                    TCommon.expr_lst_to_dot_expr 
                      [s; TCommon.expr_of_str fml_id])), 
                  Suffixed (
                    is_valid_template param_tp_id, 
                    AST.Prog.ArgList ([i], None)
                  )
                );
              }
            ]
          end
          | 2 -> assert false
          | _ -> assert false
        ) @ (generate_is_valid_4_fmls rest)
      end
    end

  let generate_is_valid_4_ctors 
    (ctors : AST.TopDecl.datatype_ctor_t list) = 
    match List.length ctors with
    | 1 -> begin 
      let ctors = NonEmptyList.coerce ctors in
      let ctor, _ = NonEmptyList.uncons ctors in
      match ctor with AST.TopDecl.DataCtor (_, _, fmls) ->
      let is_formals_valid_lst = generate_is_valid_4_fmls fmls in
      TCommon.expr_lst_to_and is_formals_valid_lst
    end
    | _ -> assert false

  let generate_is_valid_4_datatype (dtp : AST.TopDecl.datatype_t) = 
    let _, t_id, _, ctors = dtp in
    let expr = generate_is_valid_4_ctors (NonEmptyList.as_list ctors) in
    AST.TopDecl.Predicate (
      None, 
      false, 
      [], TCommon.expr_to_id (is_valid_template t_id), 
      [], [AST.TopDecl.Formal (s_id, TCommon.tp_of_id t_id)], 
      [], 
      expr
    )

end
