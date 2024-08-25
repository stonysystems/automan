open Syntax
open Internal


module AST = AnnotationPass
module Refinement = Refinement.Refinement
module TCommon = TranslatorCommon.TranslatorCommon
module Printer = Printer.PrinterAnnotation

module Translator = struct 
  let remapper = new NameRemapper.name_remapper

  module Type = struct 

    let rec t_name_seg (x : AST.Type.name_seg_t) = 
      let x_str = Printer.Type.print_name_seg x in
      match remapper#is_tp_in_config x_str with
      | true -> remapper#get_from_config x_str
      | false ->
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

  module Prog = struct

    let t_type_option (tp : AST.Type.t option) =
      match tp with 
      | Some tp -> Some (Type.translate tp)
      | None -> None

    let rec t_extended_patten (x : AST.Prog.extended_pattern_t) = 
      match x with
      | EPatLit _ -> x
      | EPatVar (id, tpo) -> (
        EPatVar (
          id, 
          t_type_option tpo
        )
      )
      | EPatCtor (ido, pats) -> 
        EPatCtor (ido, List.map t_extended_patten pats)

    let rec t_pattern (x : AST.Prog.pattern_t) = 
      match x with
      | PatVar (id, tpo) -> AST.Prog.PatVar (
        id, 
        t_type_option tpo
      )
      | PatCtor (ido, pats) -> AST.Prog.PatCtor (
        ido,
        List.map t_pattern pats
      )

    let rec t_expr_option (expr : AST.Prog.expr_t option) =
      match expr with 
      | Some expr -> Some (t_expr expr)
      | None -> None

    and t_expr (x : AST.Prog.expr_t) = 
      match x with
      | Suffixed (e, sfx) -> (
        let t_e = t_expr e in
        let t_e = (
          match sfx with 
          | ArgList _ -> (
            let id = Printer.Prog.print_expr_in_one_line t_e in
            match String.contains id '.' with
            | true -> assert false
            | false -> (
              let t_id = (
                match remapper#is_tp_in_config id with 
                | true -> 
                  Printer.Type.print_name_seg 
                    (remapper#get_from_config id)
                | false -> remapper#id_remap id
              ) in
              TCommon.expr_of_str t_id
            )
          )
          | _ -> t_e
        ) in
        let t_sfx = t_suffix sfx in
        AST.Prog.Suffixed (t_e, t_sfx)
      )
      | NameSeg name_seg -> (
        let id, tp_lst = name_seg in 
        let t_tp_lst = List.map Type.translate tp_lst in
        AST.Prog.NameSeg (id, t_tp_lst)
      ) 
      | Lambda (lst, e) -> (
        let t_lst = List.map (
          fun x ->
            let id, tp_option = x in 
            (
              id, 
              t_type_option tp_option
            )
        ) lst in
        let t_e = t_expr e in
        AST.Prog.Lambda (t_lst, t_e)
      )
      | MapDisplay e_lst -> (
        let t_e_lst = List.map (
          fun x ->
            let e1, e2 = x in
            let t_e1 = t_expr e1 in
            let t_e2 = t_expr e2 in
            (t_e1, t_e2)
        ) e_lst in
        AST.Prog.MapDisplay t_e_lst
      )
      | SeqDisplay x -> (
        let t_x = t_seq_display x in
        AST.Prog.SeqDisplay t_x
      )
      | SetDisplay x -> (
        let t_x = List.map t_expr x in
        AST.Prog.SetDisplay t_x
      )
      | If (e1, e2, e3) -> (
        let t_e1 = t_expr e1 in
        let t_e2 = t_expr e2 in
        let t_e3 = t_expr e3 in
        AST.Prog.If (t_e1, t_e2, t_e3)
      )
      | Match (expr, case_exprs) -> AST.Prog.Match (
        t_expr expr,
        List.map t_case_expr case_exprs
      )
      | Quantifier {qt = qt; qdom = qdom; qbody = qbody} -> 
        AST.Prog.Quantifier {
          qt = qt;
          qdom = t_qdom qdom;
          qbody = t_expr qbody
        }
      | SetComp (qdom, expro) -> AST.Prog.SetComp (
        t_qdom qdom,
        t_expr_option expro
      )
      | StmtInExpr _ -> assert false
      | Let {ghost = ghost; pats = pats; defs = defs; body = body} -> 
        AST.Prog.Let {
          ghost = ghost;
          pats = NonEmptyList.map t_pattern pats;
          defs = NonEmptyList.map t_expr defs;
          body = t_expr body
        }
      | MapComp {qdom = qdom; key = key; valu = valu} -> AST.Prog.MapComp {
        qdom = t_qdom qdom;
        key = t_expr_option key;
        valu = t_expr valu
      }
      | Lit _ -> x
      | This -> x
      | Cardinality expr -> AST.Prog.Cardinality (t_expr expr)
      | Tuple exprs -> AST.Prog.Tuple (List.map t_expr exprs)
      | Unary (uop, expr) -> (
        let t_expr = t_expr expr in
        AST.Prog.Unary (uop, t_expr)
      )
      | Binary (bop, e1, e2) -> AST.Prog.Binary (
        bop,
        t_expr e1,
        t_expr e2
      )
      | Lemma {lem = lem; e = e} -> AST.Prog.Lemma {
        lem = t_expr lem;
        e = t_expr e
      }
    
    and t_suffix (x : AST.Prog.suffix_t) = 
      match x with
      | AugDot augmented_dotsuffix -> (
        let dotsuffix, tp_lst = augmented_dotsuffix in
        let t_dotsuffix = (
          match dotsuffix with
          | DSRequires | DSReads | DSDig _ -> dotsuffix
          | DSId id -> (
            match (Filename.check_suffix id "?") with 
            | true -> (
              let len = String.length id in
              let id = String.sub id 0 (len - 1) in
              let t_id = (
                match remapper#is_tp_in_config id with 
                | true -> 
                  Printer.Type.print_name_seg 
                    (remapper#get_from_config id)
                | false -> remapper#id_remap id
              ) in
              Syntax.Common.DSId t_id
            )
            | false -> dotsuffix
          )
        ) in
        let t_tp_lst = List.map Type.translate tp_lst in
        AST.Prog.AugDot (t_dotsuffix, t_tp_lst)
      )
      | DataUpd x -> AST.Prog.DataUpd (
        NonEmptyList.map t_member_binding_upd x
      )
      | Subseq {lb = lb; ub = ub} -> AST.Prog.Subseq {
        lb = t_expr_option lb;
        ub = t_expr_option ub;
      }
      | SliceLen {sublens = sublens; to_end = to_end;} -> 
        AST.Prog.SliceLen {
          sublens = NonEmptyList.map t_expr sublens;
          to_end = to_end
        }
      | SeqUpd {idx = idx; v = v; } -> AST.Prog.SeqUpd {
        idx = t_expr idx;
        v = t_expr v;
      }
      | Sel expr -> Sel (t_expr expr)
      | ArgList (exprs, args) -> AST.Prog.ArgList (
        List.map t_expr exprs,
        args
      )

    and t_member_binding_upd (x : AST.Prog.member_binding_upd_t) = 
      let either, e = x in
      (either, t_expr e)

    and t_seq_display (x : AST.Prog.seq_display_t) = 
      match x with
      | SeqEnumerate exprs -> (
        let t_exprs = List.map t_expr exprs in
        AST.Prog.SeqEnumerate t_exprs 
      )
      | SeqTabulate {gen_inst = gen_inst; len = len; func = func} -> (
        let t_gen_inst = List.map Type.translate gen_inst in
        let t_len = t_expr len in
        let t_func = t_expr func in
        AST.Prog.SeqTabulate
          {gen_inst = t_gen_inst; len = t_len; func = t_func}
      )

    and t_case_expr (x : AST.Prog.case_expr_t) = 
      match x with Case (attrs, ext_pat, expr) ->
        AST.Prog.Case (
          attrs, 
          t_extended_patten ext_pat, 
          t_expr expr
        )

    and t_qvar_decl (x : AST.Prog.qvar_decl_t) = 
      match x with QVar (id, tpo, expro, attrs) -> AST.Prog.QVar (
        id,
        t_type_option tpo,
        t_expr_option expro,
        attrs
      )

    and t_qdom (x : AST.Prog.qdom_t) = 
      let AST.Prog.QDom {qvars = qvars; qrange = qrange} = x in
      AST.Prog.QDom {
        qvars = List.map t_qvar_decl qvars;
        qrange = t_expr_option qrange
      }

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

    let t_function_spec (x : AST.TopDecl.function_spec_t) = 
      match x with
      | Requires  expr -> AST.TopDecl.Requires  (Prog.t_expr expr)
      | Reads     expr -> AST.TopDecl.Reads     (Prog.t_expr expr)
      | Ensures   expr -> AST.TopDecl.Ensures   (Prog.t_expr expr)
      | Decreases expr -> AST.TopDecl.Decreases (Prog.t_expr expr)

    let t_function 
      (x : AST.TopDecl.function_t) = 
      let get_args_from_fmls fmls = 
        let rec aux lst = 
          match lst with 
          | [] -> []
          | h :: rest -> (
            match h with AST.TopDecl.Formal (id, _) ->
            (TCommon.expr_of_str id) :: (aux rest)
          ) in
        aux fmls
      in
      let args_to_assignee args = 
        let expr_to_pat e = 
          AST.Prog.PatVar (
            TCommon.expr_to_id e, None
        )
        in
        let args = NonEmptyList.coerce args in
        NonEmptyList.map expr_to_pat args
      in
      let get_self_call_from_func_id_and_args
        (func_id : string)
        (args    : AST.Prog.expr_t list) = 
        AST.Prog.Suffixed (
          TCommon.expr_of_str func_id, 
          AST.Prog.ArgList (
            args, None
          )
        )
      in
      match x with 
      | Predicate (metadata, _, _, id, _, origin_fmls, specs, e) -> begin
        let _ = metadata, e in
        let fmls_input, fmls_rtn = (
          match metadata with 
          | None -> 
            origin_fmls, [AST.TopDecl.Formal ("", TCommon.tp_of_id "bool")]
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
        let t_original_fmls = List.map t_formal origin_fmls in
        let t_fmls_input = List.map t_formal fmls_input in
        let t_fmls_rtn = List.map t_formal fmls_rtn in
        let t_rtn = Type.translate rtn in
        let t_specs = 
          (
            let valids = 
              Refinement.generate_checker_4_fmls 
                t_fmls_input 
                Refinement.is_valid_token
                false
            in
            List.map (
              fun x -> AST.TopDecl.Requires x
            ) valids
          ) @
          (List.map t_function_spec specs) @ (
            let t_args = get_args_from_fmls t_fmls_input in
            let modes = (
              match metadata with 
              | None -> []
              | Some modes -> modes
            ) in
            let pos_of_output = 
              let rec aux lst idx = 
                match lst with 
                | [] -> []
                | h :: rest -> (
                  match h with 
                  | Syntax.Annotation.Input -> aux rest (idx + 1)
                  | Syntax.Annotation.Output -> 
                    idx :: (aux rest (idx + 1))
                ) in
              aux modes 0
            in
            let args_for_l_call = 
              Refinement.generate_abstractify_4_formals
                origin_fmls 
                t_original_fmls 
                false
            in
            match List.length pos_of_output with
            | 0 -> (
              let c_call = get_self_call_from_func_id_and_args t_id t_args in
              let l_call = 
                get_self_call_from_func_id_and_args id args_for_l_call in
              let check = AST.Prog.Binary (Syntax.Common.Eq, c_call, l_call) in
              [AST.TopDecl.Ensures check]
            )
            | _ -> (
              let t_rtn = get_args_from_fmls fmls_rtn in
              let assignee = args_to_assignee t_rtn in
              let self_call = get_self_call_from_func_id_and_args t_id t_args in
              let rtn_valids = 
                Refinement.generate_checker_4_fmls 
                  t_fmls_rtn
                  Refinement.is_valid_token
                  false
              in
              let binding = AST.Prog.Let {
                ghost = false;
                pats = assignee;
                defs = NonEmptyList.coerce [self_call];
                body = TCommon.expr_lst_to_and [
                  TCommon.expr_lst_to_and rtn_valids;
                  get_self_call_from_func_id_and_args id args_for_l_call
                ]
              } in
              [AST.TopDecl.Ensures binding]
            )
          ) in
        let t_function = AST.TopDecl.Function (
          true,
          [], t_id,
          [], t_fmls_input, t_rtn,
          t_specs, 
          t_e
        ) in
        [AST.TopDecl.PredFunDecl t_function]
      end
      | Function _ -> []

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
