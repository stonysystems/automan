open Internal


module AST = Syntax.AST(TranslatorMetadata.TranslationMetaData)
module TCommon = TranslatorCommon.TranslatorCommon

module Refinement  = struct
  let remapper = new NameRemapper.name_remapper

  let s_id = "s"
  let s = TCommon.expr_of_str s_id

  let i_id = "i"
  let i = TCommon.expr_of_str i_id

  let is_valid_token = "IsValid"
  let is_abstractable_token = "IsAbstractable"
  let abstractify_seq_token = TCommon.expr_of_str "AbstractifySeq"
  let abstractify_set_token = TCommon.expr_of_str "AbstractifySet"
  let abstractify_map_token = TCommon.expr_of_str "AbstractifyMap"


  let generate_token t_id token = 
    TCommon.expr_of_str (Printf.sprintf "%s%s" t_id token)

  let generate_abstractify_token t_id id = 
    TCommon.expr_of_str 
      (Printf.sprintf "Abstractify%sTo%s" t_id id)

  let generate_args wrapped_as_member_access fml_id = 
    match wrapped_as_member_access with 
    | true -> (
      TCommon.expr_lst_to_dot_expr 
        [s; TCommon.expr_of_str fml_id]
    )
    | false -> TCommon.expr_of_str fml_id

  let rec generate_checker_4_fmls 
    (fmls : AST.TopDecl.formal_t list)
    (token : string)
    (wrapped_as_member_access : bool) = 
    match fmls with 
    | [] -> []
    | h :: rest -> begin
        (* TODO: check for any changes introduced with ghost formals *)
      match h with AST.TopDecl.Formal (_fml_ghost, fml_id, fml_tp) ->
      match fml_tp with 
      | TpTup _ -> assert false
      | TpName (_, name_seg_lst) -> begin
        let name_seg, _ = NonEmptyList.uncons name_seg_lst in
        let TpIdSeg {id = t_id; gen_inst = gen_inst} = name_seg in
        (
          match begin
            (
              (List.length gen_inst) > 0 &&
              not (TCommon.is_built_in_collection t_id)
            ) ||
            (TCommon.is_primitive t_id)
          end with 
          | true -> []
          | false -> (
          match List.length gen_inst with 
          | 0 -> begin 
            [AST.Prog.Suffixed (
              generate_token t_id token, 
              let e = generate_args wrapped_as_member_access fml_id in
                AST.Prog.ArgList (({positional=[e]; named=[]}, None))
              )]
          end
          | 1 -> begin (* id is set/seq or an alias to them *)
            let _, param_tp = List.unsnoc gen_inst in
            let param_tp_id = TCommon.id_of_tp param_tp in
            match TCommon.is_primitive param_tp_id with 
            | true -> []
            | false -> [
              Quantifier (None, {
                qt = Syntax.Common.Forall;
                qdom = QDom {
                  qvars = [QVar (i_id, None, None, [])];
                  qrange = None
                };
                qbody = Binary (
                  None, 
                  Syntax.Common.Implies,
                  (
                    AST.Prog.Binary (
                      None,
                      Syntax.Common.In, 
                      i, 
                      generate_args wrapped_as_member_access fml_id
                    )
                  ), 
                  Suffixed (
                    generate_token param_tp_id token, 
                    AST.Prog.ArgList ({positional=[i]; named=[]}, None)
                  )
                );
              })
            ]
          end
          | 2 -> ( (* id is map *)
            let rest, param_tp_v = List.unsnoc gen_inst in
            let _, param_tp_k = List.unsnoc rest in 
            let param_tp_k_id = TCommon.id_of_tp param_tp_k in
            let param_tp_v_id = TCommon.id_of_tp param_tp_v in
            (* TCommon.debug_print (param_tp_k_id ^ "  " ^ param_tp_v_id) ; *)
            let is_k_primitive = TCommon.is_primitive param_tp_k_id in
            let is_v_primitive = TCommon.is_primitive param_tp_v_id in
            match (is_k_primitive && is_v_primitive) with
            | true -> [] | false -> 
              [AST.Prog.Quantifier (None, {
                qt = Syntax.Common.Forall;
                qdom = QDom {
                  qvars = [QVar (i_id, None, None, [])];
                  qrange = None
                };
                qbody = (
                  let coll = generate_args wrapped_as_member_access fml_id in
                  let checker_for_k = 
                    (
                      match is_k_primitive with 
                      | true -> []
                      | false ->
                        [AST.Prog.Suffixed (
                          generate_token param_tp_k_id token, 
                          AST.Prog.ArgList ({positional=[i]; named=[]}, None)
                        )]
                    )
                  in
                  let checker_for_v = 
                    (
                      match is_v_primitive with 
                      | true -> []
                      | false ->
                        [AST.Prog.Suffixed (
                          generate_token param_tp_v_id token, 
                          AST.Prog.ArgList ({positional=[
                            AST.Prog.Suffixed (i, 
                              AST.Prog.ArgList 
                                ({positional=[coll]; named=[]}, None ) )
                          ]; named=[]}, None)
                        )]
                    )
                  in
                  let check = 
                    TCommon.expr_lst_to_and (checker_for_k @ checker_for_v) in
                  Binary (
                    None, 
                    Syntax.Common.Implies,
                    (
                      AST.Prog.Binary (
                        None,
                        Syntax.Common.In, 
                        i, 
                        generate_args wrapped_as_member_access fml_id
                      )
                    ), 
                    check
                  )
                )
              })]
          )
          | _ -> assert false
        )) @ (generate_checker_4_fmls rest token wrapped_as_member_access)
      end
    end

  let rec generate_checker_4_ctors
    (ctors : AST.TopDecl.datatype_ctor_t list)
    (token : string)
    (dtp_id : string) = 
    match List.length ctors with
    | 1 -> begin 
      let ctors = NonEmptyList.coerce ctors in
      let ctor, _ = NonEmptyList.uncons ctors in
      match ctor with AST.TopDecl.DataCtor (_, _t_id, fmls) ->
      let is_formals_valid_lst = generate_checker_4_fmls fmls token true in
      let extended_lst = 
        match token with 
        | "IsValid" -> begin 
          AST.Prog.Suffixed (
            generate_token dtp_id is_abstractable_token, 
            AST.Prog.ArgList ({positional=[s]; named=[]}, None)
          ) :: is_formals_valid_lst
        end
        | _ -> is_formals_valid_lst in
      TCommon.expr_lst_to_and extended_lst
    end
    | _ -> 
      let get_case_expr (ctor : AST.TopDecl.datatype_ctor_t)
        : AST.Prog.case_expr_t = 
        let expr = generate_checker_4_ctors [ctor] token dtp_id in
        match ctor with AST.TopDecl.DataCtor (_, id, fmls) ->
        let ids = List.map 
          (fun x -> match x with AST.TopDecl.Formal (_, id, _) -> id)
          fmls 
        in
        let pats = 
          List.map (fun x -> AST.Prog.EPatVar (x, None)) ids
        in
        let expr = 
          match TCommon.is_expr_blank expr with
          | true -> TCommon.expr_of_str "true"
          | false -> expr
        in
        AST.Prog.Case (
          [], 
          EPatCtor (Some id, pats),
          expr
        )
      in
      AST.Prog.Match (
        None, s, List.map get_case_expr ctors
      )

  let generate_checker_4_datatype   
    (dtp : AST.TopDecl.datatype_t)
    (token : string) = 
    let m, attrs, t_id, params, ctors = dtp in
    let _ = m, attrs, params in
    let ctors = NonEmptyList.as_list ctors in
    let expr = generate_checker_4_ctors ctors token t_id in
    let expr = 
      (
        match TCommon.is_expr_blank expr with
        | true -> TCommon.expr_of_str "true"
        | false -> expr
      )
    in
    AST.TopDecl.Predicate (
      Moder.Definitions.Predicate (* Changed for MetaData *), 
      false, 
      [], TCommon.expr_to_id (generate_token t_id token), 
      [], [AST.TopDecl.Formal (false (* FIXME *), s_id, TCommon.tp_of_id t_id)], 
      [], 
      expr
    )

  let generate_is_valid_4_datatype dtp = 
    generate_checker_4_datatype dtp is_valid_token

  let generate_is_abstractable_4_datatype dtp = 
    generate_checker_4_datatype dtp is_abstractable_token

  (* ------- Below is for abstractify ------- *)
  
  let generate_abstractify_4_formals
    (fmls   : AST.TopDecl.formal_t list)
    (t_fmls : AST.TopDecl.formal_t list)
    (wrapped_as_member_access : bool) = 
    let rec aux lst =
      match lst with
      | [] -> []
      | h :: rest -> (
        let fml, t_fml = h in
        (* TODO: check for any changes introduced with ghost formals *)
        match fml   with AST.TopDecl.Formal (_fml_ghost, fml_id,     tp) ->
        match t_fml with AST.TopDecl.Formal (_t_fml_ghost, t_fml_id, t_tp) ->
        let _ = t_fml_id in
        let tp_id,    tp_gen_inst   = TCommon.id_and_gen_inst_of_tp tp    in
        let t_tp_id,  t_tp_gen_inst = TCommon.id_and_gen_inst_of_tp t_tp  in
        match (
          (List.length tp_gen_inst) > 0 &&
          not (TCommon.is_built_in_collection tp_id)
        ) with 
        | true (* Leave it for user *) -> TCommon.expr_blank 
        | false ->
        let member_access = 
          generate_args wrapped_as_member_access fml_id in
        match TCommon.is_primitive tp_id with 
        | true -> member_access
        | false -> begin
          match List.length tp_gen_inst with 
          | 0 -> begin 
            (* AbstractifyCReplicaConstantsToLReplicaConstants(s.constants) *)
            AST.Prog.Suffixed (
                generate_abstractify_token t_tp_id tp_id, 
                let e = member_access in AST.Prog.ArgList 
                  (({positional=[e]; named=[]}, None))
              )
          end
          | 1 -> begin 
            match t_tp_id with 
            | "CBroadcast" -> (* Hard coded *)
              AST.Prog.Suffixed (
                  TCommon.expr_of_str 
                    "AbstractifyCBroadcastToRlsPacketSeq", 
                  let e = member_access in AST.Prog.ArgList 
                    (({positional=[e]; named=[]}, None))
                )
            | "OutboundPackets" -> (* Hard coded *)
              AST.Prog.Suffixed (
                  TCommon.expr_of_str 
                    "AbstractifyOutboundCPacketsToSeqOfRslPackets", 
                  let e = member_access in AST.Prog.ArgList 
                    (({positional=[e]; named=[]}, None))
                )
            | _ ->
            (* AbstractifySeq(s.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber),  *)
            let _, param_tp   = List.unsnoc tp_gen_inst   in
            let param_tp_id   = TCommon.id_of_tp param_tp in
            let _, param_tp   = List.unsnoc t_tp_gen_inst in
            let t_param_tp_id = TCommon.id_of_tp param_tp in
            match TCommon.is_primitive param_tp_id with
            | true -> member_access
            | false ->  
              let token = (
                match tp_id with 
                | "set" -> abstractify_set_token
                | _ -> abstractify_seq_token
              ) in
              AST.Prog.Suffixed (
                token, 
                AST.Prog.ArgList ((
                  {
                    positional = [                 
                      member_access; 
                      generate_abstractify_token t_param_tp_id param_tp_id]; 
                    named = []
                  }
                , None))
              )
          end
          | 2 -> (
            let r, param_tp_v = List.unsnoc tp_gen_inst in
            let param_tp_id_v = TCommon.id_of_tp param_tp_v in
            let _, param_tp_k = List.unsnoc r in
            let param_tp_id_k = TCommon.id_of_tp param_tp_k in

            let r, t_param_tp_v = List.unsnoc t_tp_gen_inst in
            let t_param_tp_id_v = TCommon.id_of_tp t_param_tp_v in
            let _, t_param_tp_k = List.unsnoc r in
            let t_param_tp_id_k = TCommon.id_of_tp t_param_tp_k in

            let argv_2, argv_4 = 
            (
              match (
                (TCommon.is_primitive param_tp_id_k) ||
                (TCommon.is_primitive t_param_tp_id_k)
              ) with 
              | true -> 
                (TCommon.expr_of_str "NoChange", 
                  TCommon.expr_of_str "NoChange")
              | false ->
                (
                  (generate_abstractify_token 
                    t_param_tp_id_k param_tp_id_k)
                  ,
                  (generate_abstractify_token 
                    param_tp_id_k t_param_tp_id_k)
                )
            )
            in
            let argv_3 = 
            (
              match (
                (TCommon.is_primitive param_tp_id_v) ||
                (TCommon.is_primitive t_param_tp_id_v)
              ) with 
              | true -> TCommon.expr_of_str "NoChange"
              | false ->
                generate_abstractify_token
                  t_param_tp_id_v param_tp_id_v
            )
            in
            AST.Prog.Suffixed (
              abstractify_map_token, 
              AST.Prog.ArgList ((
                {
                  positional = [                 
                    member_access; 
                    argv_2 ; argv_3 ; argv_4]; 
                  named = []
                }
              , None))
            )
          )
          | _ -> assert false
        end

      ) :: (aux rest)
    in
    let zipped_fmls = List.combine fmls t_fmls in
    aux zipped_fmls

  let generate_abstractify_4_ctors 
    (ctors   : AST.TopDecl.datatype_ctor_t list)
    (t_ctors : AST.TopDecl.datatype_ctor_t list) = 
    let rec aux lst = 
      match lst with 
      | [] -> []
      | h :: rest -> (
        let ctor, t_ctor = h in 
        match ctor    with AST.TopDecl.DataCtor (_, id,     fmls) ->
        match t_ctor  with AST.TopDecl.DataCtor (_, t_id, t_fmls) ->
          let abs_4_fmls = generate_abstractify_4_formals fmls t_fmls true in
          let _ = t_id in
          AST.Prog.Suffixed (
            TCommon.expr_of_str id, 
            AST.Prog.ArgList (({positional=abs_4_fmls; named=[]}, None))
          )
      ) :: (aux rest)
    in
    let zipped_ctors = List.combine ctors t_ctors in
    let abs_4_ctors = aux zipped_ctors in
    abs_4_ctors

  let generate_abstractify_4_datatype 
    (dtp    : AST.TopDecl.datatype_t)
    (t_dtp  : AST.TopDecl.datatype_t) = 
    let (_, _,   id, _,    ctors) =    dtp in 
    let (_, _, t_id, _,  t_ctors) =  t_dtp in
    let   ctors = NonEmptyList.as_list    ctors in
    let t_ctors = NonEmptyList.as_list  t_ctors in 
    let abs_4_ctors = generate_abstractify_4_ctors ctors t_ctors in
    let e = 
      match List.length abs_4_ctors with 
      | 0 -> TCommon.expr_blank
      | 1 -> let _, h = List.unsnoc abs_4_ctors in h
      | _ -> (
        let rec aux lst = 
          match lst with
          | [] -> []
          | h :: rest -> (
            let pat, abs_4_ctor = h in
            AST.Prog.Case ([],pat, abs_4_ctor) 
          ) :: (aux rest)
        in
        let t_ctors_pats = List.map (
          fun x -> match x with AST.TopDecl.DataCtor (_, id, fmls) -> 
            let fml_ids = List.map 
              (fun x -> match x with AST.TopDecl.Formal (_, id, _) -> id)
              fmls 
            in
            let pats = 
              List.map (fun x -> AST.Prog.EPatVar (x, None)) fml_ids
            in
            AST.Prog.EPatCtor (Some id, pats)
        ) t_ctors in
        let zipped = List.combine t_ctors_pats abs_4_ctors in
        AST.Prog.Match (None, s, aux zipped)
      )
    in
    AST.TopDecl.Function(
      false, 
      [], 
      TCommon.expr_to_id (generate_abstractify_token t_id id), 
      [], 
      [AST.TopDecl.Formal (false (* FIXME *), s_id, TCommon.tp_of_id t_id)], 
      TCommon.tp_of_id id, 
      [AST.TopDecl.Requires (
        AST.Prog.Suffixed (
          generate_token t_id is_abstractable_token, 
          AST.Prog.ArgList ({positional=[s]; named=[]}, None)
        )
      )], 
      e
    )

  end
