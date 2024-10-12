open Syntax
open Internal
open TypeTableBuilder

module Tracker = DataTracker.DataTracker

module AST = AST(TranslatorMetadata.TranslationMetaData)
module Refinement = Refinement.Refinement
module TCommon = TranslatorCommon.TranslatorCommon
module Printer = Printer.PrettyPrinter(TranslatorMetadata.TranslationMetaData)


module Translator = struct 
  (* remapper : should be replaced by meta data later *)
  let remapper = new NameRemapper.name_remapper

  module Type = struct 

    let rec t_name_seg (x : AST.Type.name_seg_t) = 
      let x_str = Printer.Type.print_name_seg x in
      match remapper#is_tp_in_config x_str with
      | true -> remapper#get_from_config x_str
      | false ->
        let TpIdSeg { id = id; gen_inst = gen_inst } = x in
        let x' = 
        AST.Type.TpIdSeg {
          id = remapper#id_remap id; (* NOTICE: what about alias ? *)
          gen_inst = List.map translate gen_inst
        }
        in
        x'

    and translate (x : AST.Type.t) = 
      match x with
      | TpName (m, name_seg_lst) -> AST.Type.TpName (
          m, 
          NonEmptyList.map t_name_seg name_seg_lst
        )
      | TpTup t_lst -> AST.Type.TpTup (List.map translate t_lst)

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
      | If (m, e1, e2, e3) -> (
        let t_e1 = t_expr e1 in
        let t_e2 = t_expr e2 in
        let t_e3 = t_expr e3 in
        AST.Prog.If (m, t_e1, t_e2, t_e3)
      )
      | Match (m, expr, case_exprs) -> AST.Prog.Match (
        m, 
        t_expr expr,
        List.map t_case_expr case_exprs
      )
      | Quantifier (m, {qt = qt; qdom = qdom; qbody = qbody}) -> 
        AST.Prog.Quantifier (m, {
          qt = qt;
          qdom = t_qdom qdom;
          qbody = t_expr qbody
        })
      | SetComp {qdom = qdom; body = body} -> AST.Prog.SetComp {
        qdom = t_qdom qdom;
        body = t_expr_option body
      }
      | StmtInExpr _ -> assert false
      | Let {ghost = ghost; pats = pats; defs = defs; body = body} -> 
        AST.Prog.Let {
          ghost = ghost;
          pats = NonEmptyList.map t_pattern pats;
          defs = NonEmptyList.map t_expr defs;
          body = t_expr body
        }
      | MapComp {imap = imap; qdom = qdom; key = key; valu = valu} -> AST.Prog.MapComp {
        imap = imap;
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
      | Binary (m, bop, e1, e2) -> AST.Prog.Binary (
        m, 
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
              Syntax.Common.DSId (t_id ^ "?")
            )
            | false -> dotsuffix
          )
        ) in
        let t_tp_lst = List.map Type.translate tp_lst in
        AST.Prog.AugDot (t_dotsuffix, t_tp_lst)
      )
      | DataUpd (meta, x) -> AST.Prog.DataUpd (
        meta, NonEmptyList.map t_member_binding_upd x
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
      | ArgList (args, m) -> AST.Prog.ArgList (
        t_arglist args,
        m
      )

    and t_member_binding_upd (x : AST.Prog.member_binding_upd_t) = 
      let either, e = x in
      (either, t_expr e)

    and t_arglist (x : AST.Prog.arglist_t) : AST.Prog.arglist_t = 
      match x with {positional = p; named = n} ->
      {
        positional = List.map t_expr p;
        named = List.map (
          fun x -> let id, expr = x in (id, t_expr expr)
        ) n
      }

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
      match x with Formal (ghost, id, tp) ->
        let t_tp = Type.translate tp in
        AST.TopDecl.Formal (ghost, id, t_tp)

    let t_datatype_ctor (x : AST.TopDecl.datatype_ctor_t) = 
      match x with DataCtor (attr_lst, id, formals) ->
      let _ = attr_lst in
      let t_id = remapper#id_remap id in
      let t_formals = List.map t_formal formals in
      let x' = AST.TopDecl.DataCtor ([], t_id, t_formals) in
      (* TCommon.debug_print (Printer.TopDecl.print_datatype_ctor x 0);
      TCommon.debug_print (Printer.TopDecl.print_datatype_ctor x' 0); *)
      x'

    let t_data_type_decl (x : AST.TopDecl.datatype_t) = 
      let m, attr_lst, id, generic_params, ctors = x in
      let _ = attr_lst in (* IGNORE: attr_lst *)
      let _ = generic_params in (* IGNORE: generic_params *)
      let t_id = remapper#id_remap id in
      let t_ctors = 
        NonEmptyList.coerce (
          List.map t_datatype_ctor (NonEmptyList.as_list ctors)
        )
      in
      let t_datatype = (m, attr_lst, t_id, [], t_ctors) in
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

    let t_synonym_type (x : AST.TopDecl.synonym_type_t) = 
      let t_id = remapper#id_remap x.id in
      let m_id = "s" in
      let t_rhs, fml, t_fml = (
            match x.rhs with 
            | AST.TopDecl.Synonym tp -> 
              let t_tp = (Type.translate tp) in
              AST.TopDecl.Synonym t_tp, 
              (AST.TopDecl.Formal (false, m_id, tp)), 
              (AST.TopDecl.Formal (false, m_id, t_tp))
            | _ -> assert false
          ) in
      let _ = t_id, t_rhs, fml, t_fml in
      let abstractable_body = 
        (
          let is_abstractables = 
            Refinement.generate_checker_4_fmls  
              [t_fml] Refinement.is_abstractable_token false
          in
          match is_abstractables with 
          | [] -> TCommon.expr_of_str "true"
          | h :: _ -> h
        )
      in
      let is_abstractable = 
        AST.Prog.Suffixed (
          Refinement.generate_token 
            t_id Refinement.is_abstractable_token, 
          AST.Prog.ArgList 
            ({positional=[TCommon.expr_of_str m_id]; named=[]}, None)
        )
      in
      let valid_body = 
        (
          let is_valids = 
            Refinement.generate_checker_4_fmls  
              [t_fml] Refinement.is_valid_token false
          in
          TCommon.expr_lst_to_and (is_abstractable :: is_valids)
        )
      in
      let abstractify_body = 
        (
          let abs = 
          Refinement.generate_abstractify_4_formals 
            [t_fml] [fml] false
          in
          match abs with 
          | [] -> assert false
          | h :: _ -> h
        )
      in
      let _ = valid_body, abstractable_body, abstractify_body in
      [
        AST.TopDecl.SynonymTypeDecl 
          {x with id = t_id ; rhs = t_rhs ;} ;

        AST.TopDecl.PredFunDecl (
          AST.TopDecl.Predicate (
            Moder.Definitions.Predicate , 
            false, 
            [], TCommon.expr_to_id 
                (Refinement.generate_token t_id Refinement.is_abstractable_token), 
            [], [AST.TopDecl.Formal (false, m_id, TCommon.tp_of_id t_id)], 
            [], 
            abstractable_body
          )) ;

        AST.TopDecl.PredFunDecl (
          AST.TopDecl.Predicate (
            Moder.Definitions.Predicate , 
            false, 
            [], TCommon.expr_to_id 
                (Refinement.generate_token t_id Refinement.is_valid_token), 
            [], [AST.TopDecl.Formal (false, m_id, TCommon.tp_of_id t_id)], 
            [], 
            valid_body
          )) ;

        AST.TopDecl.PredFunDecl (
          AST.TopDecl.Function(
            false, 
            [], 
            TCommon.expr_to_id 
              (Refinement.generate_abstractify_token t_id x.id), 
            [], 
            [AST.TopDecl.Formal (false, m_id, TCommon.tp_of_id t_id)], 
            TCommon.tp_of_id x.id, 
            [AST.TopDecl.Requires (
              is_abstractable
            )], 
            abstractify_body
          )) ;
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
              (* TODO: check for any changes introduced with ghost formals *)
            match h with AST.TopDecl.Formal (_ghost, id, _) ->
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
        let args : AST.Prog.arglist_t = {
          positional = args; 
          named = []
        } in
        AST.Prog.Suffixed (
          TCommon.expr_of_str func_id, 
          AST.Prog.ArgList (
            args, None (* Changed for MetaData *)
          )
        )
      in
      let get_fmls_input_and_rtn origin_fmls metadata = 
        match metadata with 
        | None -> 
          origin_fmls, [AST.TopDecl.Formal (false, "", TCommon.tp_of_id "bool")]
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
      in
      let get_rtn_from_fmls fmls_rtn =
        match List.length fmls_rtn with
        | 1 -> (
          let _, h = List.unsnoc fmls_rtn in
          (* TODO: check for changes introduced by ghost formals *)
          match h with AST.TopDecl.Formal (_ghost, _, tp) -> tp
        )
        | _ -> (
          let rec aux lst = 
            match lst with 
            | [] -> []
            | h :: rest -> (
                (* TODO: check for changes introduced by ghost formals *)
              match h with AST.TopDecl.Formal (_ghost, _, tp) -> 
                tp :: (aux rest)
            )
          in
          AST.Type.TpTup (aux fmls_rtn)
        )
      in
      let get_specs_4_refinement
        origin_fmls t_original_fmls
        fmls_rtn t_fmls_rtn
        id t_id
        original_specs 
        t_fmls_input
        metadata
        = 
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
      (List.map t_function_spec original_specs) @ (
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
          (**
            * In this step we are dealing with 
            *   function -> function method
            *)
          let pats_of_ids (ids : string list) = 
            NonEmptyList.coerce 
              (List.map 
                (fun id -> AST.Prog.PatVar (id, None)) ids)
          in
          let rtn_ids = List.map
            (fun f -> 
              match f with AST.TopDecl.Formal(_, id, _) -> id) fmls_rtn 
          in
          let t_rtn_ids = List.map
          (fun f -> 
            match f with AST.TopDecl.Formal(_, id, _) -> id) t_fmls_rtn 
          in
          let rtn_ids, t_rtn_ids = 
          (
            match rtn_ids with 
            | h :: [] -> 
              if h = "" then
                ["lr"], ["cr"]
              else
                rtn_ids, t_rtn_ids
            | _ -> rtn_ids, t_rtn_ids
          )
          in
          let c_call = 
            get_self_call_from_func_id_and_args t_id t_args in
          let l_call = 
            get_self_call_from_func_id_and_args id args_for_l_call in
          let fmls_rtn_with_tid = 
            (
              let rec aux lst  = 
                match lst with 
                | [] -> []
                | h :: rest ->
                  let t_id, fml = h in
                  match fml with AST.TopDecl.Formal (b, _id, tp) ->
                  AST.TopDecl.Formal (b, t_id, tp) :: (aux rest)
              in
              let lst = List.combine t_rtn_ids fmls_rtn in
              aux lst
            )
          in
          let c_tuples = 
            Refinement.generate_abstractify_4_formals 
              fmls_rtn_with_tid
              t_fmls_rtn
              false
          in
          let l_tuples =
            List.map TCommon.expr_of_str rtn_ids 
          in
          let is_valids = 
            Refinement.generate_checker_4_fmls
              t_fmls_rtn
              Refinement.is_valid_token
              false
          in
          let check = AST.Prog.Binary (
            None, Syntax.Common.Eq, 
            AST.Prog.Tuple c_tuples, 
            AST.Prog.Tuple l_tuples
          ) in
          let body = 
            TCommon.expr_lst_to_and (is_valids @ [check])
          in
          (* Put everything together *)
          let let_c_call = 
            AST.Prog.Let {
              ghost = false ;
              pats = (pats_of_ids t_rtn_ids) ;
              defs = NonEmptyList.coerce [c_call] ;
              body = body ;
            }
          in
          let let_l_call = 
            AST.Prog.Let {
              ghost = false ;
              pats = (pats_of_ids rtn_ids) ;
              defs = NonEmptyList.coerce [l_call] ;
              body = let_c_call ;
            }
          in
          [AST.TopDecl.Ensures let_l_call]
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
      )
      in
      (* Note by Ti
       * Note that, for each input or output formal, we need to know its 
       * original position in the predicate list to construct the refinement
       * check. Moder MetaData is not enough, we need the original 
       * Annotator MetaData.
       **)
      let predicate_decl_t_metadata_roll_back 
        (m : TranslatorMetadata.TranslationMetaData.predicate_decl_t)
        (origin_fmls : AST.TopDecl.formal_t list) :
        Annotator.AnnotationMetaData.predicate_decl_t =  
        match m with 
        | Moder.Definitions.Predicate -> 
          (* TCommon.debug_print ("here") ; *)
          None
        | Moder.Definitions.Function m -> 
          (* To be changed later *)
          let rec is_fml_in_lst 
            (lst : Annotator.AnnotationPass.TopDecl.formal_t list)
            (fml : AST.TopDecl.formal_t) : bool = 
            match lst with 
            | [] -> false
            | h :: rest -> (
              match h   with Formal (_, id , _) ->
              match fml with Formal (_, id', _) ->
                (id = id') || (is_fml_in_lst rest fml)
            )
          in
          let vars_in = m.vars_in in
          (* TCommon.debug_print (string_of_int (List.length vars_in)) ; *)
          let rec aux 
            (lst : AST.TopDecl.formal_t list) :
            (Annotation.mode_t list) = 
            match lst with 
            | [] -> []
            | h :: rest -> (
              match is_fml_in_lst vars_in h with 
              | true -> Annotation.Input
              | false -> Annotation.Output
            ) :: (aux rest)
          in
          Some (aux origin_fmls)
      in
      match x with 
      | Predicate (metadata, _, _, id, _, origin_fmls, specs, e) -> begin
        let in_ou_metadata = 
          predicate_decl_t_metadata_roll_back metadata origin_fmls in

        let fmls_input, fmls_rtn = 
          get_fmls_input_and_rtn origin_fmls in_ou_metadata in
        
        let rtn = get_rtn_from_fmls fmls_rtn in
        let t_e = 
          (
            match metadata with 
            | Moder.Definitions.Predicate -> 
              (Prog.t_expr e)
            | Moder.Definitions.Function meta -> (
              match meta.make_stub with 
              | true -> TCommon.expr_blank
              | false ->
                let tracker = Tracker.API.build fmls_rtn in
                let members_to_output = 
                  List.map (
                    fun x ->
                      match x with AST.TopDecl.Formal (_, id, _) ->
                        TCommon.expr_of_str id 
                  ) fmls_rtn in
                let t_e = 
                  Functionalization.Functionalization.entry
                    e tracker members_to_output
                in 
                let t_e = Prog.t_expr t_e in
                t_e
            )
          )
        in
        let t_id = remapper#id_remap id in
        let t_original_fmls = List.map t_formal origin_fmls in
        let t_fmls_input = List.map t_formal fmls_input in
        let t_fmls_rtn = List.map t_formal fmls_rtn in
        let t_rtn = Type.translate rtn in
        let t_specs = 
          get_specs_4_refinement
            origin_fmls t_original_fmls
            fmls_rtn t_fmls_rtn
            id t_id
            specs 
            t_fmls_input
            in_ou_metadata
        in
        let t_rtn = 
          match t_rtn with
          | TpName _ -> t_rtn
          | TpTup lst -> (
            match List.length lst with 
            | 0 -> TCommon.tp_of_id "bool"
            | _ -> t_rtn
          )
        in
        let t_function = AST.TopDecl.Function (
          true,
          [], t_id,
          [], t_fmls_input, t_rtn,
          t_specs, 
          t_e
        ) in
        [AST.TopDecl.PredFunDecl t_function]
      end
      | Function (
        is_method, 
        attrs, id, 
        params, origin_fmls, origin_rtn,
        specs,
        e
      ) ->
        let rtn_to_fmls rtn base_name = 
          match rtn with 
          | AST.Type.TpName _ -> [AST.TopDecl.Formal (false, base_name, rtn)] (* TODO: check for changes introduced by ghost formals *)
          | AST.Type.TpTup tps -> (
            let rec aux lst cnt = 
              match lst with
              | [] -> []
              | h :: rest -> 
                ((
                  AST.TopDecl.Formal (
                    false, (* TODO: check for changes introduced by ghost formals *)
                    base_name ^ (string_of_int cnt), 
                    h
                  ) :: (aux rest (cnt + 1))
                ))
            in
            aux tps 0
          )
        in
        let _ = attrs, params, is_method in
        let t_e = Prog.t_expr e in
        let t_id = remapper#id_remap id in
        let t_original_fmls = List.map t_formal origin_fmls in
        let t_fmls_input = List.map t_formal origin_fmls in
        let t_rtn = Type.translate origin_rtn in
        let fmls_rtn = rtn_to_fmls origin_rtn "lr" in
        let t_fmls_rtn = rtn_to_fmls t_rtn "cr" in
        let t_specs = 
          get_specs_4_refinement
            origin_fmls t_original_fmls
            fmls_rtn t_fmls_rtn
            id t_id
            specs 
            t_fmls_input
            None
        in
        let t_function = AST.TopDecl.Function (
          true,
          [], t_id,
          [], t_fmls_input, t_rtn,
          t_specs, 
          t_e
        ) in
        [AST.TopDecl.PredFunDecl t_function]

    let rec translate 
      (x : Syntax.Common.topdecl_modifier_t list * AST.TopDecl.t')
      (type_table : TypeTableBuilder.t) = 
      let modifier_lst, t' = x in
      let _ = modifier_lst in (* IGNORE: modifier *)
      List.map (fun x -> ([], x)) (translate' t' type_table)

    and translate' (x : AST.TopDecl.t') (type_table : TypeTableBuilder.t) = 
      match x with 
      | ModuleImport _ 
      | MethLemDecl _ -> []
      | SynonymTypeDecl x ->
        t_synonym_type x
      | ModuleDef x -> t_module_def x type_table
      | DatatypeDecl x -> (
        (* TCommon.debug_print (Printer.TopDecl.print' (DatatypeDecl x) 0) ; *)
        t_data_type_decl x
      )
      | PredFunDecl x -> t_function x

    and t_module_def 
      (x : AST.TopDecl.module_def_t) (type_table : TypeTableBuilder.t) = 
      let attribute_lst, id, t_lst = x in
      let _ = attribute_lst in (* IGNORE: attribute_lst *)
      let _ = TypeTableBuilder.find_visible_decls type_table id in
      [AST.TopDecl.ModuleDef begin
        [], 
        (remapper#module_id_remap id), 
        List.concat (List.map 
          (fun x -> translate x type_table) t_lst)
      end]
  end

  let translate (x : AST.t) (type_table : TypeTableBuilder.t) = 
    let _ = type_table in
    let Dafny { includes = _; decls = decls } = x in
    AST.Dafny { includes = [""]; decls =  
      List.concat (List.map 
        (fun x -> TopDecl.translate x type_table) decls)
    }

end
