open Syntax
open Internal


module AST = AnnotationPass
module Refinement = Refinement.Refinement
module TCommon = TranslatorCommon.TranslatorCommon

module Translator = struct 
  let remapper = new NameRemapper.name_remapper

  module Type = struct 

    let rec t_name_seg (x : AST.Type.name_seg_t) = 
      let TpIdSeg { id = id; gen_inst = gen_inst } = x in
      AST.Type.TpIdSeg {
        id = remapper#id_remap id; (* NOTICE: what about alias ? *)
        gen_inst = List.map translate gen_inst
      }

    and translate (x : AST.Type.t) = 
      match x with
      | TpName name_seg_lst -> TpName begin 
        NonEmptyList.coerce begin
          List.map t_name_seg (NonEmptyList.as_list name_seg_lst)
        end end
      | TpTup t_lst -> TpTup (List.map translate t_lst)

  end

  module TopDecl = struct 

    let t_formal (x : AST.TopDecl.formal_t) = 
      match x with Formal (id, tp) ->
        let t_tp = Type.translate tp in
        AST.TopDecl.Formal (id, t_tp)

    let t_datatype_ctor (x : AST.TopDecl.datatype_ctor_t) = 
      match x with DataCtor (attr_lst, id, formals) ->
      let _ = attr_lst in
      let t_id = remapper#id_remap id in
      let t_formals = List.map t_formal formals in
      AST.TopDecl.DataCtor ([], t_id, t_formals)

    let t_data_type_decl (x : AST.TopDecl.datatype_t) = 
      let attr_lst, id, generic_params, ctors = x in
      let _ = attr_lst in (* IGNORE: attr_lst *)
      let _ = generic_params in (* IGNORE: generic_params *)
      let t_id = remapper#id_remap id in
      let t_ctors = 
        NonEmptyList.coerce (
          List.map t_datatype_ctor (NonEmptyList.as_list ctors)
        )
      in
      let t_datatype = ([], t_id, [], t_ctors) in
      let is_valid = 
        Refinement.generate_is_valid_4_datatype         t_datatype in
      let is_abstractable = 
        Refinement.generate_is_abstractable_4_datatype  t_datatype in
      let abstractify = 
        Refinement.generate_abstractify_4_datatype    x t_datatype in
      [
        AST.TopDecl.DatatypeDecl  t_datatype      ;
        AST.TopDecl.PredFunDecl   is_valid        ;
        AST.TopDecl.PredFunDecl   is_abstractable ;
        AST.TopDecl.PredFunDecl   abstractify     ;
      ]

    let t_function 
      (x : AST.TopDecl.function_t) = 
      match x with 
      | Predicate (metadata, _, _, id, _, origin_fmls, specs, e) -> begin
        let _ = metadata, e in
        let fmls_input, fmls_rtn = (
          match metadata with 
          | None -> origin_fmls, 
                      [AST.TopDecl.Formal ("", TCommon.tp_of_id "bool")]
          | Some metadata -> (
            let rec aux lst = 
              match lst with 
              | [] -> [], []
              | h :: rest -> (
                let fmls_input', fmls_rtn' = aux rest in
                let mode, fml = h in 
                match mode with 
                | Syntax.Annotation.Input  -> (fml :: fmls_input', fmls_rtn')
                | Syntax.Annotation.Output -> (fmls_input', fml :: fmls_rtn')
              )
            in
            let mode_lst = metadata in
            let zipped = List.combine mode_lst origin_fmls in
            aux zipped
          )
        ) in
        let rtn = 
          match List.length fmls_rtn with
          | 1 -> (
            let _, h = List.unsnoc fmls_rtn in 
            match h with AST.TopDecl.Formal (_, tp) -> tp
          )
          | _ -> (
            let rec aux lst = 
              match lst with 
              | [] -> []
              | h :: rest -> (
                match h with AST.TopDecl.Formal (_, tp) -> 
                  tp :: (aux rest)
              )
            in
            AST.Type.TpTup (aux fmls_rtn)
          )
        in
        let t_e = TCommon.expr_of_str "HOLDER" in
        let t_id = remapper#id_remap id in
        let t_function = AST.TopDecl.Function (
          true,
          [], t_id,
          [], fmls_input, rtn,
          specs, 
          t_e
        ) in
        [AST.TopDecl.PredFunDecl t_function]
      end
      | Function _ -> []

    (* type t = Common.topdecl_modifier_t list * t' *)
    let rec translate 
      (x : Syntax.Common.topdecl_modifier_t list * AST.TopDecl.t') = 
      let modifier_lst, t' = x in
      let _ = modifier_lst in (* IGNORE: modifier *)
      List.map (fun x -> ([], x)) (translate' t')

    and translate' (x : AST.TopDecl.t') = 
      match x with 
      | ModuleImport _ 
      | SynonymTypeDecl _ 
      | MethLemDecl _ -> []
      | ModuleDef x -> t_module_def x
      | DatatypeDecl x -> t_data_type_decl x
      | PredFunDecl x -> t_function x

    and t_module_def (x : AST.TopDecl.module_def_t) = 
      let attribute_lst, id, t_lst = x in
      let _ = attribute_lst in (* IGNORE: attribute_lst *)
      [AST.TopDecl.ModuleDef begin
        [], 
        (remapper#module_id_remap id), 
        List.concat (List.map translate t_lst)
      end]
  end

  let translate (x : AST.t) = 
    let Dafny { includes = _; decls = decls } = x in
    AST.Dafny { includes = [""]; decls = begin 
      List.concat (List.map TopDecl.translate decls)
    end }
      
end
