open Syntax
open Internal
open TypeTableBuilder


module TCommon = TranslatorCommon.TranslatorCommon
module Tracker = DataTracker.DataTracker
module QuantifierHelper = QuantifierHelper.QuantifierHelper

module ModerAST = AST(Moder.ModingMetaData)
module TranslatorAST = AST(TranslatorMetadata.TranslationMetaData)
module AnnotationToTranslator = 
  Convert
    (Annotator.AnnotationMetaData)
    (TranslatorMetadata.TranslationMetaData)

module Converter = struct

  module Type = struct 
    let rec convert_name_seg 
      (x : ModerAST.Type.name_seg_t) : TranslatorAST.Type.name_seg_t = 
      match x with ModerAST.Type.TpIdSeg x ->
      TranslatorAST.Type.TpIdSeg
      {id = x.id;
        gen_inst = List.map convert_t x.gen_inst}

    and convert_t 
      (x : ModerAST.Type.t) : TranslatorAST.Type.t = 
      match x with 
      | ModerAST.Type.TpName (meta, name_segs) -> 
        let name_segs' = NonEmptyList.map convert_name_seg name_segs in
        let meta' = meta in
        TranslatorAST.Type.TpName (meta', name_segs')
      | ModerAST.Type.TpTup ts -> 
        let ts' = List.map convert_t ts in 
        TranslatorAST.Type.TpTup ts'

    and convert_generic_params 
      (x : ModerAST.Type.generic_params_t) : 
      TranslatorAST.Type.generic_params_t = x

    let convert_t_option 
      (x : ModerAST.Type.t option) : TranslatorAST.Type.t option = 
      match x with 
      | Some x -> Some (convert_t x)
      | None -> None
  end

  let convert_augmented_dotsuffix 
  (x : ModerAST.augmented_dotsuffix_t) 
    : TranslatorAST.augmented_dotsuffix_t = 
    let (dotsuffixs, types) = x in
    let types' = List.map Type.convert_t types in
    (dotsuffixs, types')

  module Prog = struct 

    let convert_name_seg 
      (x : ModerAST.Prog.name_seg_t) : TranslatorAST.Prog.name_seg_t = 
      let (id, tps) = x in
      (id, List.map Type.convert_t tps)

    let rec convert_extended_pattern 
      (x : ModerAST.Prog.extended_pattern_t) :
      TranslatorAST.Prog.extended_pattern_t = 
      match x with 
      | EPatLit lit -> TranslatorAST.Prog.EPatLit lit
      | EPatVar (id, tpo) ->
        TranslatorAST.Prog.EPatVar (
          id, Type.convert_t_option tpo
        )
      | EPatCtor (ido, extended_patterns) ->
        TranslatorAST.Prog.EPatCtor (
          ido, 
          List.map convert_extended_pattern extended_patterns
        )

    let rec convert_pattern 
      (x : ModerAST.Prog.pattern_t) : TranslatorAST.Prog.pattern_t = 
      match x with 
      | PatVar (id, tpo) -> 
        TranslatorAST.Prog.PatVar (id, Type.convert_t_option tpo)
      | PatCtor (ido, patterns) ->
        TranslatorAST.Prog.PatCtor (
          ido, 
          List.map convert_pattern patterns
        )

    let rec convert_expr 
      (x : ModerAST.Prog.expr_t) : TranslatorAST.Prog.expr_t = 
      match x with 
      | Suffixed (expr, suffix) -> 
        let expr' = convert_expr expr in
        let suffix' = convert_suffix suffix in
        TranslatorAST.Prog.Suffixed (expr', suffix')
      | NameSeg name_seg -> 
        let name_seg' = convert_name_seg name_seg in
        TranslatorAST.Prog.NameSeg name_seg'
      | Lambda (id_with_tp_lst, expr) ->
        let id_with_tp_lst' = List.map (
          fun x ->
            let (id, tpo) = x in 
            (id, Type.convert_t_option tpo)
        ) id_with_tp_lst in
        let expr' = convert_expr expr in
        TranslatorAST.Prog.Lambda (id_with_tp_lst', expr')
      | MapDisplay lst ->
        let lst' = List.map (
          fun x ->
            let (e1, e2) = x in
            (convert_expr e1, convert_expr e2)
        ) lst in 
        TranslatorAST.Prog.MapDisplay lst'
      | SeqDisplay seq_display ->
        TranslatorAST.Prog.SeqDisplay 
          (convert_seq_display seq_display)
      | SetDisplay exprs ->
        let exprs' = List.map convert_expr exprs in
        TranslatorAST.Prog.SetDisplay exprs'
      | If (meta, e1, e2, e3) ->
        (* It has to be none if the converter is triggered *)
        let _ = meta in 
        let meta' = None in 
        let e1' = convert_expr e1 in
        let e2' = convert_expr e2 in
        let e3' = convert_expr e3 in
        TranslatorAST.Prog.If (meta', e1', e2', e3')
      | Match (meta, expr, case_exprs) ->
        (* It has to be none if the converter is triggered *)
        let _ = meta in 
        let meta' = None in
        let expr' = convert_expr expr in
        let case_exprs' = List.map convert_case_expr case_exprs in
        TranslatorAST.Prog.Match (meta', expr', case_exprs')
      | Quantifier (meta, quantification) ->
        (* It has to be none if the converter is triggered *)
        let _ = meta in 
        let meta' = None in
        let quantification' = convert_quantification quantification in 
        TranslatorAST.Prog.Quantifier (meta', quantification')
      | SetComp set_comp ->
        TranslatorAST.Prog.SetComp (convert_set_comp set_comp)
      | StmtInExpr _ -> 
        TranslatorCommon.assert_helper 
          false
          "Checker: StmtInExpr is not implemented yet." ;
        assert false
      | Let x -> 
        TranslatorAST.Prog.Let
        {
          ghost = x.ghost ; 
          pats = NonEmptyList.map convert_pattern x.pats ;
          defs = NonEmptyList.map convert_expr x.defs ;
          body = convert_expr x.body ;
        }
      | MapComp map_comp -> 
        TranslatorAST.Prog.MapComp
          (convert_map_comp map_comp)
      | Lit lit -> 
        TranslatorAST.Prog.Lit lit
      | This ->
        TranslatorAST.Prog.This
      | Cardinality expr -> 
        TranslatorAST.Prog.Cardinality (convert_expr expr)
      | Tuple exprs -> 
        TranslatorAST.Prog.Tuple 
          (List.map convert_expr exprs)
      | Unary (uop, expr) -> 
        TranslatorAST.Prog.Unary 
          (uop, convert_expr expr)
      | Binary (meta, bop, e1, e2) -> 
        (* It has to be none if the converter is triggered *)
        let _ = meta in 
        let meta' = None in 
        let e1' = convert_expr e1 in 
        let e2' = convert_expr e2 in
        TranslatorAST.Prog.Binary (meta', bop, e1', e2')
      | Lemma x ->
        TranslatorAST.Prog.Lemma 
          {
            lem = convert_expr x.lem ; 
            e = convert_expr x.e ;
          }

    and convert_expr_option 
      (x : ModerAST.Prog.expr_t option) : TranslatorAST.Prog.expr_t option = 
      match x with 
      | Some x -> Some (convert_expr x)
      | None -> None

    and convert_suffix 
      (x : ModerAST.Prog.suffix_t) : TranslatorAST.Prog.suffix_t = 
      match x with 
      | ModerAST.Prog.AugDot augmented_dotsuffix -> 
        let augmented_dotsuffix' = 
          convert_augmented_dotsuffix augmented_dotsuffix in
        TranslatorAST.Prog.AugDot augmented_dotsuffix'
      | ModerAST.Prog.DataUpd 
          (meta, member_binding_upds) ->
        let meta' = meta in 
        let member_binding_upds' = 
          NonEmptyList.map convert_member_binding_upd member_binding_upds in
        TranslatorAST.Prog.DataUpd (meta', member_binding_upds')
      | ModerAST.Prog.Subseq subseq ->
        let subseq' = convert_subseq subseq in
        TranslatorAST.Prog.Subseq subseq'
      | ModerAST.Prog.SliceLen x -> 
        TranslatorAST.Prog.SliceLen
        {
          sublens = NonEmptyList.map convert_expr x.sublens;
          to_end = x.to_end;
        }
      | ModerAST.Prog.SeqUpd x -> 
        TranslatorAST.Prog.SeqUpd
        {
          idx = convert_expr x.idx;
          v = convert_expr x.v;
        }
      | ModerAST.Prog.Sel expr -> 
        let expr' = convert_expr expr in
        TranslatorAST.Prog.Sel expr'
      | ModerAST.Prog.ArgList (arglist, meta) ->
        let arglist' = convert_arglist arglist in
        let meta' = meta in
        TranslatorAST.Prog.ArgList (arglist', meta')

    and convert_subseq 
      (x : ModerAST.Prog.subseq_t) : TranslatorAST.Prog.subseq_t = 
      {
        lb = convert_expr_option x.lb;
        ub = convert_expr_option x.ub;
      }

    and convert_seq_displat 
      (x : ModerAST.Prog.seq_display_t) : TranslatorAST.Prog.seq_display_t = 
      match x with 
      | SeqEnumerate exprs -> TranslatorAST.Prog.SeqEnumerate (
        List.map convert_expr exprs
      )
      | SeqTabulate x -> TranslatorAST.Prog.SeqTabulate {
        gen_inst = List.map Type.convert_t x.gen_inst ;
        len = convert_expr x.len ;
        func = convert_expr x.func
      }
    
    and convert_member_binding_upd 
      (x : ModerAST.Prog.member_binding_upd_t) :
      TranslatorAST.Prog.member_binding_upd_t = 
      let (either, expr) = x in
      let expr' = convert_expr expr in
      (either, expr')

    and convert_arglist 
      (x : ModerAST.Prog.arglist_t) :
      TranslatorAST.Prog.arglist_t = 
      {
        positional = List.map convert_expr x.positional;
        named = List.map (
          fun x ->
            let (id, expr) = x in 
            (id, convert_expr expr)
        ) x.named
      }

    and convert_seq_display
      (x : ModerAST.Prog.seq_display_t) : 
      TranslatorAST.Prog.seq_display_t = 
      match x with 
      | SeqEnumerate exprs -> 
        let exprs' = List.map convert_expr exprs in
        TranslatorAST.Prog.SeqEnumerate exprs' 
      | SeqTabulate x ->
        TranslatorAST.Prog.SeqTabulate {
          gen_inst = List.map Type.convert_t x.gen_inst;
          len = convert_expr x.len;
          func = convert_expr x.func;
        }
    
    and convert_quantification
      (x : ModerAST.Prog.quantification_t) :
      TranslatorAST.Prog.quantification_t = 
      {
        qt = x.qt ; 
        qdom = convert_qdom x.qdom ; 
        qbody = convert_expr x.qbody ;
      }

    and convert_map_comp 
      (x : ModerAST.Prog.map_comp_t) :
      TranslatorAST.Prog.map_comp_t = 
      {
        imap = x.imap ; 
        qdom = convert_qdom x.qdom ;
        key = convert_expr_option x.key ;
        valu = convert_expr x.valu ;
      }

    and convert_set_comp 
      (x : ModerAST.Prog.set_comp_t) :
      TranslatorAST.Prog.set_comp_t = 
      {
        qdom = convert_qdom x.qdom ; 
        body = convert_expr_option x.body ;
      }

    and convert_attribute 
      (x : ModerAST.Prog.attribute_t) : TranslatorAST.Prog.attribute_t = 
      let (str, exprs) = x in
      let exprs' = List.map convert_expr exprs in
      (str, exprs')

    and convert_case_expr 
      (x : ModerAST.Prog.case_expr_t) : TranslatorAST.Prog.case_expr_t = 
      match x with ModerAST.Prog.Case (attrs, ext_pat, expr) ->
        let attrs' = List.map convert_attribute attrs in
        let ext_pat' = convert_extended_pattern ext_pat in
        let expr' = convert_expr expr in
        TranslatorAST.Prog.Case (attrs', ext_pat', expr')

    and convert_qvar_decl
      (x : ModerAST.Prog.qvar_decl_t) : TranslatorAST.Prog.qvar_decl_t = 
      match x with QVar (id, tpo, expro, attrs) ->
        TranslatorAST.Prog.QVar (
          id, 
          Type.convert_t_option tpo, 
          convert_expr_option expro, 
          List.map convert_attribute attrs
        )
    
    and convert_qdom 
      (x : ModerAST.Prog.qdom_t) : TranslatorAST.Prog.qdom_t = 
      match x with QDom x -> 
        TranslatorAST.Prog.QDom {
          qvars = List.map convert_qvar_decl x.qvars ; 
          qrange = convert_expr_option x.qrange ; 
        }

    and convert_lhs
      (x : ModerAST.Prog.lhs_t) : TranslatorAST.Prog.lhs_t = 
      convert_expr x 
    
    and convert_rhs
      (x : ModerAST.Prog.rhs_t) : TranslatorAST.Prog.rhs_t = 
      let (expr, attrs) = x in
      (
        convert_expr expr, 
        List.map convert_attribute attrs
      )

    and convert_var_decl 
      (x : ModerAST.Prog.var_decl_t) : TranslatorAST.Prog.var_decl_t = 
      match x with DeclIds (
        var_decl_id_lhss, var_decl_ids_rhso
      ) ->
        TranslatorAST.Prog.DeclIds (
          List.map convert_var_decl_id_lhs var_decl_id_lhss, 
          (
            match var_decl_ids_rhso with 
            | Some var_decl_ids_rhs -> 
              Some (convert_var_decl_ids_rhs var_decl_ids_rhs)
            | None -> None
          )
        )

    and convert_var_decl_id_lhs
      (x : ModerAST.Prog.var_decl_id_lhs_t) :
      TranslatorAST.Prog.var_decl_id_lhs_t = 
      {
        id = x.id ; 
        tp = Type.convert_t_option x.tp ;
        attrs = List.map convert_attribute x.attrs ;
      }

    and convert_var_decl_ids_rhs
      (x : ModerAST.Prog.var_decl_ids_rhs_t) : 
      TranslatorAST.Prog.var_decl_ids_rhs_t = 
      match x with Assign rhss ->
        TranslatorAST.Prog.Assign (
          List.map convert_rhs rhss 
        )

  end

  module TopDecl = struct 

    let convert_formal 
      (x : ModerAST.TopDecl.formal_t) : 
      TranslatorAST.TopDecl.formal_t = 
      match x with Formal (b, id, tp) ->
        TranslatorAST.TopDecl.Formal (
          b, id, Type.convert_t tp
        )

    let convert_datatype_ctor 
      (x : ModerAST.TopDecl.datatype_ctor_t) :
      TranslatorAST.TopDecl.datatype_ctor_t = 
      match x with DataCtor (
        attrs, id, fmls
      ) -> TranslatorAST.TopDecl.DataCtor (
        List.map Prog.convert_attribute attrs, 
        id, 
        List.map convert_formal fmls
      )

    let convert_datatype 
      (x : ModerAST.TopDecl.datatype_t) :
      TranslatorAST.TopDecl.datatype_t = 
      let (meta, attrs, id, params, ctors) = x in
      let meta' = meta in
      let attrs' = List.map Prog.convert_attribute attrs in
      let id' = id in 
      let params' = Type.convert_generic_params params in
      let ctors' = NonEmptyList.map convert_datatype_ctor ctors in
      (meta', attrs', id', params', ctors')

    let convert_synonym_type_rhs 
      (x : ModerAST.TopDecl.synonym_type_rhs_t) :
      TranslatorAST.TopDecl.synonym_type_rhs_t = 
      match x with 
      | Synonym tp -> 
        TranslatorAST.TopDecl.Synonym 
          (Type.convert_t tp)
      | Subset (id, tpo, expr) ->
        TranslatorAST.TopDecl.Subset 
          (id, Type.convert_t_option tpo, Prog.convert_expr expr)

    let convert_synonym_type
      (x : ModerAST.TopDecl.synonym_type_t) :
      TranslatorAST.TopDecl.synonym_type_t = 
      {
        ann = x.ann ;
        attrs = List.map Prog.convert_attribute x.attrs ;
        id = x.id ; 
        params = Type.convert_generic_params x.params ;
        rhs = convert_synonym_type_rhs x.rhs ;
      }

    let convert_function_spec 
      (x : ModerAST.TopDecl.function_spec_t) :
      TranslatorAST.TopDecl.function_spec_t = 
      match x with 
      | Requires e -> 
        TranslatorAST.TopDecl.Requires
          (Prog.convert_expr e)
      | Reads e -> 
        TranslatorAST.TopDecl.Reads
          (Prog.convert_expr e)
      | Ensures e -> 
        TranslatorAST.TopDecl.Ensures
          (Prog.convert_expr e)
      | Decreases e -> 
        TranslatorAST.TopDecl.Decreases
          (Prog.convert_expr e)

    let convert_function
      (x : ModerAST.TopDecl.function_t) :
      TranslatorAST.TopDecl.function_t = 
      match x with 
      | Predicate 
        (meta, b, attrs, id, params, fmls, specs, e) ->
          TranslatorAST.TopDecl.Predicate 
          (
            meta,
            b,
            List.map Prog.convert_attribute attrs, 
            id, 
            Type.convert_generic_params params, 
            List.map convert_formal fmls, 
            List.map convert_function_spec specs, 
            Prog.convert_expr e
          )
      | Function
        (b, attrs, id, params, fmls, tp, specs, e) ->
          TranslatorAST.TopDecl.Function
          (
            b, 
            List.map Prog.convert_attribute attrs, 
            id, 
            Type.convert_generic_params params, 
            List.map convert_formal fmls, 
            Type.convert_t tp, 
            List.map convert_function_spec specs, 
            Prog.convert_expr e
          )

    let rec convert_t' 
      (x : ModerAST.TopDecl.t') : TranslatorAST.TopDecl.t' = 
      match x with 
      | ModerAST.TopDecl.ModuleImport import -> 
        TranslatorAST.TopDecl.ModuleImport import
      | ModerAST.TopDecl.ModuleDef module_def ->
        let module_def' = convert_module_def module_def in
        TranslatorAST.TopDecl.ModuleDef module_def'
      | ModerAST.TopDecl.DatatypeDecl datatype ->
        TranslatorAST.TopDecl.DatatypeDecl 
          (convert_datatype datatype)
      | ModerAST.TopDecl.SynonymTypeDecl synonym_type ->
        TranslatorAST.TopDecl.SynonymTypeDecl 
          (convert_synonym_type synonym_type)
      | ModerAST.TopDecl.PredFunDecl f ->
        TranslatorAST.TopDecl.PredFunDecl
          (convert_function f)
      | ModerAST.TopDecl.MethLemDecl _ -> 
        TranslatorCommon.assert_helper 
          false
          "Checker: MethLemDecl is not implemented yet." ;
        assert false

    and convert_t 
      (x : ModerAST.TopDecl.t) : TranslatorAST.TopDecl.t =  
      let modifiers, t' = x in (modifiers, convert_t' t')

    and convert_module_def 
      (x : ModerAST.TopDecl.module_def_t) : 
      TranslatorAST.TopDecl.module_def_t = 
      let attrs, id, ts = x in
      let attrs' = List.map Prog.convert_attribute attrs in
      let ts' = List.map convert_t ts in
      (attrs', id, ts')
  
  end

  let convert (x : ModerAST.t) : (TranslatorAST.t) = 
    match x with ModerAST.Dafny x ->
    TranslatorAST.Dafny
    {
      includes = x.includes;
      decls = List.map TopDecl.convert_t x.decls;
    }

end

module Checker = struct 

  let assert_helper = TranslatorCommon.assert_helper

  let print_checker_log = false

  module Prog = struct 
    let v_holder = TCommon.expr_of_str "holder"

    (* To be implemented: Quantifier and Match *)
    (* Ignore the eq_meta.unassigned_members at this moment: It's unassigned all the time *)
    let rec check_expr 
      (x : ModerAST.Prog.expr_t)
      (tracker : DataTracker.DataTracker.t)
      (qtf_booker : QuantifierHelper.quantifier_booker) :
      (TranslatorAST.Prog.expr_t *
       DataTracker.DataTracker.t *
       QuantifierHelper.quantifier_booker) = 
      let basic = (Converter.Prog.convert_expr x, tracker, qtf_booker) in

      if print_checker_log then
        TCommon.debug_print 
          ("[Checker] " ^ 
          (TCommon.str_of_expr (Converter.Prog.convert_expr x))) ;

      match x with 
      | Suffixed (expr, suffix) -> 
        (
          match suffix with 
          | ArgList (arglist, meta) ->
            (
              match meta with 
              | None -> basic (* Shouldn't happen *)
              | Some arglist_functionalize -> 
                let tracker' = 
                  List.fold_left 
                    (fun t x ->
                        let k, v = x in
                        Tracker.API.assign t k v) 
                    tracker
                    (List.map
                        (fun x ->
                            let k = TCommon.expr_of_outvar_lhs x in
                            let v = v_holder in
                            (k, v)
                        ) arglist_functionalize.out_vars) in
                let expr' = TranslatorAST.Prog.Suffixed ( 
                  Converter.Prog.convert_expr expr, 
                  TranslatorAST.Prog.ArgList (
                    Converter.Prog.convert_arglist arglist, 
                    meta
                )) in (expr', tracker', qtf_booker)
            )
          | _ -> basic
        ) 
      | Let x -> 
        let (body_expr', tracker', qtf_booker) = 
          check_expr x.body tracker qtf_booker
        in
        let expr' = 
          TranslatorAST.Prog.Let {
            ghost = x.ghost ; 
            pats = NonEmptyList.map 
                      Converter.Prog.convert_pattern x.pats ; 
            defs = NonEmptyList.map 
                      Converter.Prog.convert_expr x.defs ;
            body = body_expr' ;
          } in
        (expr', tracker', qtf_booker)
      | Binary (meta, bop, e1, e2) ->        
        (
          match meta with 
          | None -> assert false
          | Some binary_op_functionalize -> 
            match binary_op_functionalize with 
            | Moder.Definitions.Eq eq_meta ->
              (**
                * meta.outvar and meta.unassigned_members 
                * are not necessary  
                *)
              
              let (updated, qtf_booker) = 
                QuantifierHelper.try_add_seq_dom x qtf_booker in
              
              if updated then 
                (* let _ = QuantifierHelper.print_seq_doms qtf_booker in *)
                (Converter.Prog.convert_expr x, tracker, qtf_booker)
              else
                let k, v = 
                (match eq_meta.outvar_is_left with
                | true -> e1, e2 | false -> e2, e1) in
                let k, v = 
                  Converter.Prog.convert_expr k, 
                  Converter.Prog.convert_expr v in
                let tracker' = Tracker.API.assign tracker k v in
                (TranslatorAST.Prog.Binary
                  (meta, bop,
                    Converter.Prog.convert_expr e1,
                    Converter.Prog.convert_expr e2), tracker', qtf_booker)
            
            | Moder.Definitions.And _ ->
              (**
                * meta is not useful at all; 
                *)
              let clean_tracker = Tracker.API.clear tracker in

              let e1', tracker_l, qtf_booker = check_expr e1 clean_tracker qtf_booker in
              let lft_vars = 
                List.map
                (fun x : Moder.Definitions.outvar_lhs_t -> 
                  let id = TCommon.str_of_expr x in
                  { mq_outvar = NonEmptyList.coerce [id] ; 
                    fieldlike = None ; } ) 
                (Tracker.API.get_assigned_lst tracker_l) in

              let e2', tracker_r, qtf_booker = check_expr e2 clean_tracker qtf_booker in
              let rht_vars = 
                List.map
                (fun x : Moder.Definitions.outvar_lhs_t -> 
                  let id = TCommon.str_of_expr x in
                  { mq_outvar = NonEmptyList.coerce [id] ; 
                    fieldlike = None ; } ) 
                (Tracker.API.get_assigned_lst tracker_r) in
              let meta' = 
                Some (Moder.Definitions.And {
                  conj_left  = lft_vars ; 
                  conj_right = rht_vars ;
                }) in
              let tracker' = Tracker.API.merge tracker tracker_l in
              let tracker' = Tracker.API.merge tracker' tracker_r in
              let x' = TranslatorAST.Prog.Binary 
                (meta', bop, e1', e2') in
              (x', tracker', qtf_booker)
        )
      | If (meta, e_cond, e_then, e_else) ->
        (
          match meta with 
          | None -> basic
          | Some meta ->
          let empty_tracker = Tracker.API.clear tracker in
          let e_cond' = Converter.Prog.convert_expr e_cond in

          let e_then', tracker_then, _ = 
            check_expr e_then empty_tracker qtf_booker in
          let e_else', tracker_else, _ = 
            check_expr e_else empty_tracker qtf_booker in

          assert_helper 
            (Tracker.API.compare tracker_then tracker_else)
            "checker: then-branch and else-branch return different set of assignments"
          ;
          
          let merged_tracker = 
            Tracker.API.merge tracker_then tracker_else in
          let vars = 
            Tracker.API.get_assigned_lst merged_tracker in
          let vars = 
            NonEmptyList.coerce vars in
          let meta' : TranslatorMetadata.Definitions.ite_functionalize_t = ({
            assigned_vars = 
              ( NonEmptyList.map
                (fun x : Moder.Definitions.outvar_lhs_t -> 
                  let id = TCommon.str_of_expr x in
                  { mq_outvar = NonEmptyList.coerce [id] ; 
                    fieldlike = None; } )
                  vars );
            branch_permutations = meta ;
          }) in
          
          (* TCommon.debug_print "start the buggy merge." ; *)
          let tracker' = Tracker.API.merge tracker merged_tracker in
          (* TCommon.debug_print "end the buggy merge." ; *)
          (* (Printf.printf "%s\n" (Tracker.show tracker') ) ; *)

          let expr' = 
            TranslatorAST.Prog.If 
              (Some meta', e_cond', e_then', e_else') in
          (expr', tracker', qtf_booker)
        ) 
      | Quantifier (_meta, quantification) -> 
        let (_is_map_dom, qtf_booker) = 
          QuantifierHelper.try_add_map_dom x qtf_booker in 
        let (is_map_map, qtf_booker) = 
          QuantifierHelper.try_add_map_map x qtf_booker in
        let (is_seq_map, qtf_booker) = 
          QuantifierHelper.try_add_seq_map x qtf_booker in
        if is_seq_map then
          (* let _ = QuantifierHelper.print_seq_maps booker_updated_seq_map in *)
          (
            match QuantifierHelper.construct_seq_display qtf_booker with
            | None -> 
              (Converter.Prog.convert_expr x, tracker, qtf_booker)
            | Some (seq_display, k) ->
              let expr' = 
                TranslatorAST.Prog.Quantifier 
                  (Some 
                    {out_var = k;
                      collection = 
                      TranslatorMetadata.Definitions.QFSeq (seq_display);}, 
                  (Converter.Prog.convert_quantification quantification))
              in 
              let k' = Converter.Prog.convert_expr k in
              (* TCommon.debug_print_expr k' ; *)
              let tracker' = Tracker.API.assign tracker k' v_holder in
              (expr', tracker', qtf_booker)
          )
        else if is_map_map then
          (
            match QuantifierHelper.construct_map_qtf qtf_booker with
            | None ->
              (Converter.Prog.convert_expr x, tracker, qtf_booker)
            | Some (qtfier, k) ->
              let expr' = 
                TranslatorAST.Prog.Quantifier
                  (Some
                    {
                      out_var = k;
                      collection = 
                        TranslatorMetadata.Definitions.QFMap (qtfier);
                    }, (Converter.Prog.convert_quantification quantification)) 
              in
              let k' = Converter.Prog.convert_expr k in
              let tracker' = Tracker.API.assign tracker k' v_holder in
              (expr', tracker', qtf_booker)
          )
        else
          (Converter.Prog.convert_expr x, tracker, qtf_booker)
      | _ -> basic

  end
  
  module TopDecl = struct 

    let check_function 
      (x : ModerAST.TopDecl.function_t) : 
      TranslatorAST.TopDecl.function_t = 
      match x with 
      | Predicate 
          (meta, is_ghost, attrs, id, params, fmls, specs, e) ->
        let _ = is_ghost, attrs, id, params, fmls, specs, e in
        (
          if print_checker_log then
            TCommon.debug_print ("[Checker] " ^ id) ;

          match meta with 
          | Moder.Definitions.Predicate -> 
            Converter.TopDecl.convert_function x
          | Moder.Definitions.Function f_meta -> (
            match f_meta.make_stub with
            | true -> Converter.TopDecl.convert_function x
            | false -> (
              let vars_out = NonEmptyList.as_list f_meta.vars_out in
              let vars_out = List.map (
                fun x ->
                  match x with 
                    Annotator.AnnotationPass.TopDecl.Formal (b, id, tp) ->
                    TranslatorAST.TopDecl.Formal (
                      b, id, (
                        AnnotationToTranslator.typ (
                          fun x -> let _ = x in None
                        ) tp
                      ))) vars_out in
              let tracker = 
                DataTracker.DataTracker.API.build vars_out in
              (* init checker analysis here *)
              let qtf_booker = QuantifierHelper.init in
              let (e', tracker', _) = Prog.check_expr e tracker qtf_booker in
              let _ = tracker' in

              (* Printf.printf "%s\n" (Tracker.show tracker') ; *)
              assert_helper
                (Tracker.API.saturation_check tracker')
                ("Saturation Check for " ^ id ^ " failed") ;
              
              TranslatorAST.TopDecl.Predicate (
                meta, 
                is_ghost, 
                List.map Converter.Prog.convert_attribute attrs, 
                id, 
                Converter.Type.convert_generic_params params, 
                List.map Converter.TopDecl.convert_formal fmls, 
                List.map Converter.TopDecl.convert_function_spec specs, 
                e'
              )
            )))

      | Function _ -> Converter.TopDecl.convert_function x

    let rec check_t 
      (x : ModerAST.TopDecl.t)
      (type_table : TypeTableBuilder.t) : 
      TranslatorAST.TopDecl.t = 
      let (modifiers, t') = x in
      (modifiers, check_t' t' type_table)

    and check_t' 
      (x : ModerAST.TopDecl.t') 
      (type_table : TypeTableBuilder.t) : 
      TranslatorAST.TopDecl.t' = 
      match x with 
      | ModuleDef module_def ->  
        TranslatorAST.TopDecl.ModuleDef
          (check_module_def module_def type_table)
      | PredFunDecl f ->
        TranslatorAST.TopDecl.PredFunDecl
          (check_function f)
      | _ -> Converter.TopDecl.convert_t' x

    and check_module_def 
      (x : ModerAST.TopDecl.module_def_t)
      (type_table : TypeTableBuilder.t) :
      TranslatorAST.TopDecl.module_def_t = 
      let (attrs, id, ts) = x in
      let _ = TypeTableBuilder.find_visible_decls type_table id in
      (
        List.map Converter.Prog.convert_attribute attrs, 
        id, 
        List.map (
          fun x ->
            check_t x type_table
        ) ts
      )

  end
  
  let check 
    (x : ModerAST.t)
    (type_table : TypeTableBuilder.t) :(TranslatorAST.t) = 
    match x with ModerAST.Dafny x ->
      TranslatorAST.Dafny
      {
        includes = x.includes;
        decls = List.map (
          fun x -> 
            TopDecl.check_t x type_table
        ) x.decls;
      }

end
