open Syntax
open Internal

module TCommon = TranslatorCommon.TranslatorCommon
module Tracker = DataTracker.DataTracker
module AST = AST(TranslatorMetadata.TranslationMetaData)

module Functionalization = struct 

  type let_helper = 
    { pats: AST.Prog.pattern_t NonEmptyList.t
    ; defs: AST.Prog.expr_t NonEmptyList.t }

  let local_var (cnter : int) : string = 
    "t" ^ (string_of_int cnter)

  let generate_tuple_access
    (var_id : string)
    (len : int) : AST.Prog.expr_t list = 
    let rec aux x = 
      match x with 
      | 0 -> [] 
      | _ -> (
        TCommon.expr_lst_to_dot_expr
          [(TCommon.expr_of_str var_id) ;
            (TCommon.expr_of_str (string_of_int (x - 1)))] 
      ) :: (aux (x - 1))
    in
    aux len

  let rec functionalizing_expr 
    (x : AST.Prog.expr_t)   (* The expr to be solved                        *)
    (tracker : Tracker.t)   (* The tracker with entries created             *)
    (cnter : int)           (* Counter to generate local variables          *)
    (members_to_be_output : AST.Prog.expr_t list) :
    (**
      * Only used when x is a if-cond ;  
      * Is it possible to remove it ?
      *)
    (
      let_helper list  *    (* The expr solved                              *)
      Tracker.t        *    (* Tracker constructed for members_to_be_output *)
      int                   (* Increased counter                            *)
    ) =   
    (* TCommon.debug_print_expr x ;
    TCommon.debug_print 
    (String.concat " + " 
      (List.map TCommon.str_of_expr members_to_be_output)) ; *)
    match x with 
    | Suffixed (callee, suffix) -> 
      (
        match suffix with 
        | ArgList (arglist, meta) ->
          (
            match meta with 
            | None -> assert false (* Shouldn't happen *)
            | Some arglist_functionalize -> 
              (**
                * In meta data, in_exprs are represented in ParserPass AST
                * That is, it cannot be used unless converted into 
                * Translator AST.
                *)
              let rec aux 
                (lst : AST.Prog.expr_t list)
                (ou_exprs : AST.Prog.expr_t list) : AST.Prog.expr_t list =
                match lst with 
                | [] -> []
                | h :: rest -> (
                  match List.exists (
                    fun x -> 
                      TCommon.is_expr_eq h x 
                  ) ou_exprs with 
                  | true -> [] | false -> [h]
                ) @ (aux rest ou_exprs)
              in
              let ou_exprs = 
                List.map 
                  TCommon.expr_of_outvar_lhs 
                  arglist_functionalize.out_vars in
              let in_exprs = 
                aux arglist.positional ou_exprs in 
              let cnter = cnter + 1 in
              let var_id = local_var cnter in
              let func_call = 
                AST.Prog.Suffixed 
                  (callee, 
                    AST.Prog.ArgList (
                      { positional = in_exprs ; named = [] ; } ,
                      None)) 
              in
              let access = 
                generate_tuple_access 
                  var_id (List.length arglist_functionalize.out_vars) in
              let access = 
                match List.length access with
                | 1 -> [TCommon.expr_of_str var_id]
                | _ -> access 
              in

              (* TCommon.debug_print (string_of_int (List.length access)) ;
              TCommon.debug_print (string_of_int (List.length members_to_be_output)) ;
              TCommon.debug_print 
                (String.concat " + " 
                  (List.map TCommon.str_of_expr members_to_be_output)) ; *)
              
              let tracker' = (* all output added *)
                List.fold_left 
                  (fun t x ->
                      let k, v = x in
                      Tracker.API.assign t k v) 
                  tracker
                  (List.combine 
                      members_to_be_output access) in
              let let_helper = {
                pats = NonEmptyList.coerce [AST.Prog.PatVar (var_id, None)] ;
                defs = NonEmptyList.coerce [func_call] ;
              } in
              ([let_helper], tracker', cnter)
          )
        | _ -> assert false
      ) 
    | Binary (meta, _, e1, e2) -> (
      match meta with 
      | None -> (
        (* TCommon.debug_print (TCommon.str_of_expr x) ; *)
        ([], tracker, cnter)
      )
      | Some binary_op_functionalize ->
      match binary_op_functionalize with 
      | Moder.Definitions.Eq eq_meta -> 
        let k, v = 
        (match eq_meta.outvar_is_left with
        | true -> e1, e2 | false -> e2, e1) in
        let cnter = cnter + 1 in
        let var_id = local_var cnter in
        let let_helper = {
          pats = NonEmptyList.coerce [AST.Prog.PatVar (var_id, None)] ;
          defs = NonEmptyList.coerce 
            [Tracker.Obligation.Prog.solve_expr tracker v] ;
        } in
        let tracker' = 
          Tracker.API.assign tracker k (TCommon.expr_of_str var_id) in
          ([let_helper], tracker', cnter)
      | Moder.Definitions.And and_meta ->
        (* let clean_tracker = 
          Tracker.API.clear tracker in *)
        let (helpers_lft, tracker, cnter) = 
          functionalizing_expr 
            e1 
            tracker 
            cnter
            (List.map 
              TCommon.expr_of_outvar_lhs and_meta.conj_left)
        in 
        let (helpers_rht, tracker, cnter) = 
        functionalizing_expr 
          e2
          tracker 
          cnter
          (List.map 
            TCommon.expr_of_outvar_lhs and_meta.conj_right)
        in
        (* let tracker' = Tracker.merge tracker  tracker_lft in
        let tracker' = Tracker.merge tracker' tracker_rht in *)
        (
          helpers_lft @ helpers_rht , 
          tracker , 
          cnter
        )
    )
    | If (meta, e_cond, e_then, e_else) ->
      (
        match meta with 
        | None -> assert false | Some meta ->
        let members_to_be_output' = 
          List.map 
            TCommon.expr_of_outvar_lhs 
            (NonEmptyList.as_list meta.assigned_vars) in
        let e_then' = 
          entry e_then tracker members_to_be_output' in
        let e_else' = 
          entry e_else tracker members_to_be_output' in
        let expr' = 
          AST.Prog.If (None, e_cond, e_then', e_else') in
        let cnter = cnter + 1 in
        let var_id = local_var cnter in
        let let_helper = {
            pats = NonEmptyList.coerce [AST.Prog.PatVar (var_id, None)] ;
            defs = NonEmptyList.coerce [expr'] ;
        } in
        let access = 
          (
            match List.length members_to_be_output' with 
            | 0 -> assert false
            | 1 -> [TCommon.expr_of_str var_id]
            | _ -> 
              generate_tuple_access 
                var_id (List.length members_to_be_output')
          )
        in
        let tracker' = (* all output added *)
          List.fold_left 
            (fun t x ->
                let k, v = x in
                Tracker.API.assign t k v) 
            tracker
            (List.combine 
                members_to_be_output' access) in
        ([let_helper], tracker', cnter)
      )
    | Let let_bind ->
      let solved_expr = 
        entry
          let_bind.body tracker members_to_be_output
      in    
      let cnter = cnter + 1 in
      let var_id = local_var cnter in
      let access = 
        generate_tuple_access 
          var_id (List.length members_to_be_output) in
      let access = 
        match List.length access with
        | 1 -> [TCommon.expr_of_str var_id]
        | _ -> access 
      in
      let tracker' = (* all output added *)
      List.fold_left 
        (fun t x ->
            let k, v = x in
            Tracker.API.assign t k v) 
        tracker
        (List.combine 
            members_to_be_output access) in
      let assigner = 
        AST.Prog.Let {
          ghost = let_bind.ghost ;
          pats = let_bind.pats ;
          defs = NonEmptyList.map 
            (fun x -> Tracker.Obligation.Prog.solve_expr tracker x) 
            let_bind.defs ;
          body = solved_expr ;
        }
      in
      let helper = {
        pats = NonEmptyList.coerce [AST.Prog.PatVar (var_id, None)] ;
        defs = NonEmptyList.coerce [assigner] ;
      } in
      ([helper], tracker', cnter)
    | Quantifier (meta, _) ->
      (
        match meta with 
        | None -> ([], tracker, cnter)
        | Some meta -> 
          let k = Checker.Converter.Prog.convert_expr meta.out_var in
          match meta.collection with 
          | QFSeq seq_display -> (
            let v = 
              AST.Prog.SeqDisplay
                (Checker.Converter.Prog.convert_seq_display seq_display) in
            let cnter = cnter + 1 in
            let var_id = local_var cnter in
            let let_helper = {
              pats = NonEmptyList.coerce [AST.Prog.PatVar (var_id, None)] ;
              defs = NonEmptyList.coerce 
                [Tracker.Obligation.Prog.solve_expr tracker v] ;
            } in
            let tracker' = 
              Tracker.API.assign tracker k (TCommon.expr_of_str var_id) in
            ([let_helper], tracker', cnter)
          )
          | QFMap comp -> (
            let comp' = Checker.Converter.Prog.convert_map_comp comp in
            let v = AST.Prog.MapComp comp' in
            let cnter = cnter + 1 in
            let var_id = local_var cnter in
            let let_helper = {
              pats = NonEmptyList.coerce [AST.Prog.PatVar (var_id, None)] ;
              defs = NonEmptyList.coerce 
                [Tracker.Obligation.Prog.solve_expr tracker v] ;
            } in
            let tracker' = 
              Tracker.API.assign tracker k (TCommon.expr_of_str var_id) in
            ([let_helper], tracker', cnter)
          )
          | _ -> assert false
      )
    | _ -> ([], tracker, cnter)

  and entry 
    (x : AST.Prog.expr_t)   (* The expr to be solved                        *)
    (tracker : Tracker.t)   (* The tracker with entries created             *)
    (members_to_be_output : (* Members should be returned by this solver    *)
      AST.Prog.expr_t list) :
      AST.Prog.expr_t       (* The expr solved                              *)
    = 
    let rec aux (* Construct the final Let-Bind expression *)
      (lst : let_helper list) (x : AST.Prog.expr_t)
      : AST.Prog.expr_t = 
      match lst with 
      | [] -> x 
      | h :: rest -> 
        let x = aux rest x in
        AST.Prog.Let {
          ghost = false ; 
          pats = h.pats ; 
          defs = h.defs ; 
          body = x 
        }
    in
    let (let_helpers, tracker, _) = 
      functionalizing_expr 
        x tracker 0 members_to_be_output in
    let outputs = 
      (Tracker.API.construct_for_members 
        tracker members_to_be_output) in
    let final_output = 
      match outputs with 
      | [] -> assert false
      | h :: [] -> h
      | _ -> AST.Prog.Tuple outputs
    in
    aux let_helpers final_output

end
