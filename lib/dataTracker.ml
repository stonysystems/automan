open Syntax
open TypeTableBuilder
open Internal


module AST = AST(TranslatorMetadata.TranslationMetaData)
module TCommon = TranslatorCommon.TranslatorCommon
module Printer = 
  Printer.PrettyPrinter(TranslatorMetadata.TranslationMetaData)
module Convert = 
  Convert (TrivMetaData) (TranslatorMetadata.TranslationMetaData)

(**
  * DataTracker is used for:
  * 1. Harmony Check: Each member cannot be assigned twice.
  * 2. Saturation Check: Each member must be assigned.
  * 3. Assisting in translating Moder MetaData to Translator MetaData,
  *    specifically determining the members created by an expression.
  *
  * DataUpdate case:
  *   An expression like s' == s.(x := s'.x) involves assigning a sub-member
  *   with the member value of the output state, which could be assigned in any
  *   other part of the logical expression.
  *  
  * We follow the assumption that for each obligation call, such as
  * s' == s.(x := s'.x), the assignment of s'.x has already been declared in 
  * the preceding context.
  *
  *)

(**
  * APIs for caller (Defined at DataTracker.AST.)
  *   assign (t, k, v)      : t
  *   build (formals)       : t
  *   saturation_check (t)  : bool
  *   compare (t1, t2)      : bool
  *   merge (t1, t2)        : t
  *   get_assigned_lst (t)  : expr list
  *   clear (t)             : t
  *   construct_for_members (t, members) : exprs
  *)

module DataTracker = struct 

  let print_log = false
  let print_tracker_built = false

  type tracker_k = AST.TopDecl.formal_t 
  [@@deriving show, eq]

  and tracker_v = 
    {
      (* Assigned value; initially null *)
      assigned_v : AST.Prog.expr_t ;

      (* Tracker for this datatype *)
      t : t ;
    }
  [@@deriving show, eq]

  (**
    * formal (d : D)
    * datatype D = D (x : X, y : Y)
    * t ->
    *   Tracker (k = (d : D), list = [v0, v1])
    *   v0 ->
    *     t ->
    *       Tracker (k = (x : X), list = []) 
    *     i.e. the key for v0 is determined by v0.t.k
    *)
  and t = | Tracker of (tracker_k * tracker_v list) 
  [@@deriving show, eq]

  let assert_helper = TranslatorCommon.assert_helper

  let fml_from_passerpass_to_translator 
    (fml : ParserPass.TopDecl.formal_t) : AST.TopDecl.formal_t = 
    match fml with ParserPass.TopDecl.Formal (is_ghost, id, tp) ->
    (
      let tp_handler_t (m : TrivMetaData.type_t) : 
        TranslatorMetadata.TranslationMetaData.type_t = 
        let _ = m in None 
      in
      let tp' = Convert.typ tp_handler_t tp
      in
      AST.TopDecl.Formal (is_ghost, id, tp')
    )

  let get_member_id_lst_from_t (t : t) : string list = 
    match t with Tracker (_, vs) ->
    let rec aux lst = 
      match lst with 
      | [] -> []
      | h :: rest -> (
        match h.t with Tracker (k, _) ->
        match k with Formal (_, id, _) ->
        id :: (aux rest)
      ) in
    aux vs

  let rec build 
    (k : tracker_k) : t = 
    match k with Formal (is_ghost, _id, tp) ->
      
      if print_log then
        TCommon.debug_print (
          "[Tracker] building " ^ (Printer.TopDecl.print_formal k)
        );

      let _ = is_ghost in
      let empty_t = Tracker (k, []) in
      match TCommon.is_tp_id tp with
      | true -> (
        let tp_id = TCommon.id_of_tp tp in
        match TypeTableBuilder.find_type_decl tp_id with 
        | Some (module_name, (modifiers, decl_body)) ->
          let _ = module_name, modifiers in (
            match decl_body with 
            | DatatypeDecl datatype -> 
              let (meta, attrs, _, params, ctors) = datatype in
              let _ = meta, attrs, params in
              (* assert_helper (id = id') "data tracker: id of data type mismatch"; *)
              let ctors_len = List.length (NonEmptyList.as_list ctors) in (
                match ctors_len with 
                | 0 ->
                  assert_helper 
                  false
                  "data tracker: no constructor; grammar error";
                assert false
                | 1 -> (
                    let (ctor, _) = NonEmptyList.uncons ctors in
                    match ctor with DataCtor (attrs, ctor_id, fmls) ->
                      (* TCommon.debug_print ctor_id ;
                      assert (1 > 2); *)

                      let _ = attrs, ctor_id in
                      let vs = List.map (
                        fun (x : tracker_k) : tracker_v -> 
                          {
                            assigned_v = TCommon.expr_blank ;
                            t = build x ;
                          }
                      ) (
                        List.map fml_from_passerpass_to_translator fmls
                      ) in
                      Tracker (k, vs)
                  )
                | _ -> 
                  assert_helper 
                    false
                    "data tracker: cannot handle multi-constructors";
                  assert false
              )
            | SynonymTypeDecl _synonym_type -> 
              if print_log then 
                TCommon.debug_print 
                  ("[Tracker] not handling alias " ^ tp_id ^ " because bugs in type table") ;

              empty_t

              (* [BUG] for Type Table : alias for 'Votes' is still 'Votes' *)
              (* if print_log then
                TCommon.debug_print 
                  ("[Tracker] goto lias " ^ (synonym_type.id))
              ;
              assert (1 > 2); *)

              (* let alias_id = (
                match synonym_type.rhs with 
                | Synonym tp -> (
                  let tp_handler_t (m : TrivMetaData.type_t) : 
                  TranslatorMetadata.TranslationMetaData.type_t = 
                  let _ = m in None 
                    in
                  let tp' = Convert.typ tp_handler_t tp in
                  TCommon.id_of_tp tp'
                )
                | _ -> assert false
              ) in

              let k' = AST.TopDecl.Formal (
                is_ghost, id, TCommon.tp_of_id alias_id) in
              build k'  *)
            
            | _ -> assert false
          )
        | None -> (
          if print_log then 
            TCommon.debug_print 
              ("[Tracker] failed to find def for " ^ tp_id) ;
          empty_t
        )
      )
      | false -> empty_t

  let is_tracker_k_equals_to_id 
    (k : tracker_k) (id : string) : bool = 
    (* TCommon.debug_print (Printer.TopDecl.print_formal k) ; *)
    match k with AST.TopDecl.Formal (_, id', _) -> id = id'
  
  let is_t_for_this_id 
    (t : t) (id : string) : bool = 
    match t with Tracker (k, _) -> is_tracker_k_equals_to_id k id
  
  (**
    * Find the wanted tracker_v from t.tracker_v list
    *)
  let query_sub_tracker_v (tracker : t) (member_id : string) : tracker_v =   
    match tracker with Tracker (_, vs) ->
      let rec aux (lst : tracker_v NonEmptyList.t) = 
        let (h, rest) = NonEmptyList.uncons lst in
        let t = h.t in
        match is_t_for_this_id t member_id  with 
        | true -> h
        | false -> aux (NonEmptyList.coerce rest)
      in
      aux (NonEmptyList.coerce vs)

  (**
    * Find a tracker from a v_lst that has a t with key = id 
    * Assing the value e' to it  
    *)
  let assign_sub_t
    (t : t)
    (member_id : string)
    (assigned_v : AST.Prog.expr_t option) 
    (sub_t : t option)
    : t = 
    
    (* TCommon.debug_print member_id ; 
    TCommon.debug_print (String.concat " - " (get_member_id_lst_from_t t)) ; *)

    match t with Tracker (t_k, t_vs) ->
    let rec aux lst : tracker_v list = 
      match lst with 
      | [] -> 
          assert_helper 
            false
            "data tracker: update failed; cannot find the member";
          assert false
      | h :: rest -> 
        match is_t_for_this_id h.t member_id with
        | true -> 
          
          (* TCommon.debug_print (TCommon.str_of_expr h.assigned_v) ; *)

          {
            assigned_v = (
              match assigned_v with 
              | None -> h.assigned_v 
              | Some v -> (
                assert_helper 
                (
                  (* This node shouldn't have been assigned before. *)
                  (TCommon.is_expr_blank h.assigned_v) ||
                  (* Otherwise the value to be assigned is null, meaning erase. *)
                  (TCommon.is_expr_blank v)
                )
                "data tracker: harmony check failed";
                v
              )
            ) ;
            t = (
              match sub_t with 
              | None -> h.t 
              | Some sub_t -> sub_t
            ) ;
          } :: rest
        | false ->
          h :: (aux rest)
    in
    let t_vs' = aux t_vs in
    Tracker (t_k, t_vs')

  (**
    * For tracker t, find the node with key = k
    * Assign value v with skipped members (only for data update)
    *)
  let assign
    (t : t)
    (k : AST.Prog.expr_t) 
    (v : AST.Prog.expr_t) 
    : t = 
    let rec aux 
      (exprs : AST.Prog.expr_t NonEmptyList.t) 
      (t : t) : t = 
      let (h, rest) = NonEmptyList.uncons exprs in
      let member_id = TCommon.str_of_expr h in

      (* TCommon.debug_print ("here " ^ member_id) ; *)

      match rest with 
      | [] -> ( 
          (**
            * Replace the target tracker_v in tracker_vs with
            * a new one with updated v and skipped_members
            *)
          assign_sub_t t member_id (Some v) None
        )
      | _ -> (
        let sub_tracker = query_sub_tracker_v t member_id in
        
        assert_helper 
          (* Unassigned before *)
          (TCommon.is_expr_blank sub_tracker.assigned_v) 
          "data tracker: harmony check failed";
        
        (* Here *)
        let sub_t' = 
          aux (NonEmptyList.coerce rest) sub_tracker.t
        in
        assign_sub_t t member_id None (Some sub_t')
      )
    in
    let exprs = TCommon.dot_expr_to_expr_lst k in
    aux (NonEmptyList.coerce exprs) t

  let erase 
    (t : t)
    (k : AST.Prog.expr_t) 
    : t = 
    assign t k (TCommon.expr_blank)

  let query_tracker_v_top_lvl 
    (tracker : t)
    (member : AST.Prog.expr_t) : tracker_v = 
    let rec aux (t : t) (member_id_lst : string NonEmptyList.t ) : tracker_v = 
      let (h, rest) = NonEmptyList.uncons member_id_lst in
      let sub_v = query_sub_tracker_v t h in
      match rest with 
      | [] -> sub_v
      | _ -> aux sub_v.t (NonEmptyList.coerce rest)
    in
    let member_lst = TCommon.dot_expr_to_expr_lst member in
    let member_id_lst = List.map (
      fun x -> TCommon.str_of_expr x
    ) member_lst in
    let member_id_lst = NonEmptyList.coerce member_id_lst in
    aux tracker member_id_lst

  let query_t_top_lvl
  (tracker : t)
  (member : AST.Prog.expr_t) : t = 
    let v = query_tracker_v_top_lvl tracker member in
    v.t

  let rec is_t_all_filled 
    (t : t) : bool = 
    match t with Tracker (_, tracker_vs) ->
      match tracker_vs with 
      | [] -> false 
      | _ -> (
        List.for_all (fun x ->
          (TCommon.is_expr_n_blank x.assigned_v) ||
          (is_t_all_filled x.t)) tracker_vs
      )

  let rec compare
    (t1 : t)
    (t2 : t) : bool = 
    let compare_two_v 
      (v1 : tracker_v)
      (v2 : tracker_v) : bool = 
      let is_v1_filled = TCommon.is_expr_n_blank v1.assigned_v in
      let is_v2_filled = TCommon.is_expr_n_blank v2.assigned_v in 
      match is_v1_filled == is_v2_filled with 
      | false ->
        (is_v1_filled && (is_t_all_filled v2.t)) || 
        (is_v2_filled && (is_t_all_filled v1.t))
      | true -> 
        match is_v1_filled with 
        | true -> true
        | false ->
          compare v1.t v2.t
    in
    match t1 with Tracker (_, t1_vs) ->
    match t2 with Tracker (_, t2_vs) ->
    List.for_all (
      fun x ->
        let v1, v2 = x in
        compare_two_v v1 v2
    ) (List.combine t1_vs t2_vs)

  let rec get_assigned_lst 
    (member_seq : AST.Prog.expr_t list) 
    (* Initially empty, indicate the visited members *)
    (t : t) : AST.Prog.expr_t list = 
    let get_member_id_for_v (v : tracker_v) : string =
      match v.t with Tracker (k, _) ->
      match k with Formal (_, id, _) -> id
    in
    match t with Tracker (_, tracker_vs) -> 
    match tracker_vs with 
    | [] -> []
    | _ -> 
      let rec aux 
        (lst : tracker_v list) : AST.Prog.expr_t list = 
      match lst with 
      | [] -> []
      | h :: rest ->
        (
          let member_seq = 
            (member_seq @ 
            [TCommon.expr_of_str 
              (get_member_id_for_v h)]) 
          in
          (
            match TCommon.is_expr_n_blank h.assigned_v with 
            | true -> 
              [TCommon.expr_lst_to_dot_expr 
                member_seq] 
            | false -> 
              get_assigned_lst member_seq h.t
          ) @ (aux rest)
        )
      in
      aux tracker_vs  

  let rec merge 
    (t1 : t)
    (t2 : t) : t = 
    let merge_two_v
      (v1 : tracker_v)
      (v2 : tracker_v) : tracker_v = 

      (* (
        match v1.t with Tracker (k, _) ->
        match k with AST.TopDecl.Formal (_, id, _) ->
        TCommon.debug_print ("checking " ^ id) ;
      ) ; *)

      let is_v1_filled = TCommon.is_expr_n_blank v1.assigned_v in
      let is_v2_filled = TCommon.is_expr_n_blank v2.assigned_v in 
      match is_v1_filled = is_v2_filled with  
      | false -> (* one is filled and the other one is not *)
        (
          (* TCommon.debug_print "filled unequal";
          TCommon.debug_print_expr v1.assigned_v ;
          TCommon.debug_print_expr v2.assigned_v ; *)
          let sub_t = merge v1.t v2.t in
          (**
            * label the node closer to root as filled 
            * in this way the generated code will be shorter
            *)
          match is_v1_filled with 
          | true ->
            (* TCommon.debug_print_expr v1.assigned_v ; *)
            {assigned_v = v1.assigned_v ;
              t = sub_t ;}
          | false ->
            (* TCommon.debug_print_expr v2.assigned_v ; *)
            {assigned_v = v2.assigned_v ;
              t = sub_t ;}
        )
      | true ->  
        let is_all_filled = is_v1_filled in
        match is_all_filled with 
        | true -> v1 | false -> 
          {
            assigned_v = v1.assigned_v ;
            t = merge v1.t v2.t ;
          }
    in
    match t1 with Tracker (k, v1_lst) ->
    match t2 with Tracker (_, v2_lst) ->
      match k with AST.TopDecl.Formal (_, _, _) ->
      (* TCommon.debug_print ("merging key (" ^ id ^ ") " ^ (string_of_int (List.length v1_lst))) ; *)
      Tracker (k, 
                (List.map 
                  (fun x -> let v1, v2 = x in (merge_two_v v1 v2))
                    (List.combine v1_lst v2_lst)))

  let query_value
    (tracker : t)
    (member : AST.Prog.expr_t) : AST.Prog.expr_t = 

    if print_log then
      TCommon.debug_print 
        ("[Tracker] " ^ "query value for " ^ (TCommon.str_of_expr member)) ;

    let v = query_tracker_v_top_lvl tracker member in
    v.assigned_v

  let rec construct (v : tracker_v) : AST.Prog.expr_t = 
    match TCommon.is_expr_n_blank v.assigned_v with
    | true -> v.assigned_v | false ->
    match v.t with Tracker (k, sub_vs) ->
    match k with AST.TopDecl.Formal (_, _, tp) ->
    let args = List.map construct sub_vs in

    assert ((List.length args) <> 0) ;
    
    let tp_id = TCommon.id_of_tp tp in
    AST.Prog.Suffixed 
      (TCommon.expr_of_str tp_id, 
        AST.Prog.ArgList 
          ({positional = args; named = []}, 
          None))

  (**
    * A module used to replace an obligation occurred inside an expression.
    * Note that we assume the assignment to this obligation has occurred 
    * in the previous analysis, that is, stored in the data tracker.
    *)
  module Obligation = struct 
    
    (**
      * Used for cases when new local variables declared by let-binding 
      * overwrite the variables of the output.
      *)
    let remove_sub_v_with_k_id (t : t) (id : string) : t = 
      let rec aux (lst : tracker_v list) : tracker_v list  = 
        match lst with 
        | [] -> []
        | h :: rest -> (
          match h.t with Tracker (tracker_k, _) ->
          match is_tracker_k_equals_to_id tracker_k id with 
          | true -> [] | false -> [h]
        ) @ (aux rest)
      in 
      match t with Tracker (tracker_k, tracker_vs) ->
        Tracker (tracker_k, aux tracker_vs)

    let is_it_an_obligation 
      (t : t)
      (id : string) : bool = 
      let member_id_lst = get_member_id_lst_from_t t in
      List.exists (fun x -> x = id) member_id_lst
      
    (**
      * Read in an expression, return an expression.
      * If the expr is in the form of 
      *   s' or s'.x.y 
      * Return an expression with the obligation occured and solved
      * Return None if no obligation occured
      *)
    let try_obligation 
      (t : t)
      (e : AST.Prog.expr_t) : AST.Prog.expr_t option = 
      match e with 
      | Suffixed (_, suffix) -> (
        match suffix with 
        | AugDot _ -> (
          let dot_lst = TCommon.dot_expr_to_expr_lst e in
          let dot_lst = NonEmptyList.coerce dot_lst in
          let h,  _  = NonEmptyList.uncons dot_lst in 
          match is_it_an_obligation t (TCommon.str_of_expr h) with 
          | true -> (
            (* TCommon.debug_print_expr e ; *)
            Some (query_value t e)
          )
          | false -> None
        )
        | _ -> None
      )
      | NameSeg name_seg -> 
        let id, tps = name_seg in 
        (
          match tps with 
          | [] -> (
            match is_it_an_obligation t id with
            | true -> 
              Some 
                (query_value t (TCommon.expr_of_str id))
            | false -> None
          )
          | _ -> None
        )
      | _ -> None

    module Prog = struct 

      let rec solve_expr (t : t) (x : AST.Prog.expr_t) : AST.Prog.expr_t = 
        match try_obligation t x with
        | Some x' -> x' | None ->
        match x with 
        | Suffixed (basic, suffix) -> (
          let basic' = solve_expr t basic in 
          let suffix' = solve_suffix t suffix in
          Suffixed (basic', suffix')
        )
        | NameSeg _ -> x
        | Lambda (lst, expr) -> 
          Lambda (lst, solve_expr t expr)
        | MapDisplay lst -> 
          MapDisplay (List.map 
            (fun x -> let e1, e2 = x in 
            (solve_expr t e1, solve_expr t e2)) lst)
        | SeqDisplay seq_display ->  
          SeqDisplay (solve_seq_desplay t seq_display)
        | SetDisplay exprs ->
          SetDisplay (List.map (fun x -> solve_expr t x) exprs)
        | If (meta, e1, e2, e3) -> 
          If (meta, 
              solve_expr t e1, 
              solve_expr t e2, 
              solve_expr t e3)
        | Match (meta , e1, case_exprs) ->
          Match (meta, 
                  solve_expr t e1, 
                  List.map (fun x -> solve_case_expr t x) case_exprs)
        | Quantifier (meta, quantification) ->
          Quantifier (meta, solve_quantification t quantification)
        | SetComp set_comp ->
          SetComp (solve_set_comp t set_comp)
        | StmtInExpr _ -> assert false
        | Let x -> (
          let rec aux 
            (t : t)
            (defs : AST.Prog.expr_t NonEmptyList.t) : t =
            let h, rest = NonEmptyList.uncons defs in
            let dot_lst = TCommon.dot_expr_to_expr_lst h in
            let dot_lst = NonEmptyList.coerce dot_lst in
            let h, _ = NonEmptyList.uncons dot_lst in
            let h = TCommon.str_of_expr h in
            let t = remove_sub_v_with_k_id t h in
            let rest = NonEmptyList.coerce rest in
            aux t rest
          in
          let t' = aux t x.defs in
          Let {
            ghost = x.ghost ; 
            pats = x.pats ; 
            defs = NonEmptyList.map (fun x -> solve_expr t' x) x.defs ;
            body = solve_expr t' x.body ;
          }
        )
        | MapComp map_comp ->
          MapComp (solve_map_comp t map_comp)
        | Lit _ -> x
        | This -> x
        | Cardinality expr -> 
          Cardinality (solve_expr t expr)
        | Tuple exprs ->
          Tuple (List.map (fun x -> solve_expr t x) exprs)
        | Unary (uop, expr) ->
          Unary (uop, solve_expr t expr)
        | Binary (meta, bop, e1, e2) ->
          Binary (meta, bop, solve_expr t e1, solve_expr t e2)
        | Lemma x ->
          Lemma { lem = solve_expr t x.lem ; e = solve_expr t x.e }
      
      and solve_expr_option
        (t : t)
        (x : AST.Prog.expr_t option) : AST.Prog.expr_t option = 
        match x with 
        | Some x -> Some (solve_expr t x)
        | None -> None

      and solve_suffix 
        (t : t) (x : AST.Prog.suffix_t) : AST.Prog.suffix_t = 
        match x with 
        | AugDot _ -> x
        | DataUpd (meta, upds) -> 
          DataUpd (meta, 
            NonEmptyList.map 
              (fun x -> solve_member_binding_upd t x) upds)
        | Subseq subseq -> 
          Subseq (solve_subseq t subseq)
        | SliceLen x ->
          SliceLen {
            sublens = NonEmptyList.map (fun x -> solve_expr t x) x.sublens ; 
            to_end = x.to_end ;
          }
        | SeqUpd x -> 
          SeqUpd {idx = solve_expr t x.idx ; v = solve_expr t x.v}
        | Sel expr -> Sel (solve_expr t expr)
        | ArgList (arglist, meta) -> 
          ArgList (solve_arglist t arglist, meta)
      
      and solve_subseq 
        (t : t) (x : AST.Prog.subseq_t) : AST.Prog.subseq_t = 
        {
          lb = solve_expr_option t x.lb ;
          ub = solve_expr_option t x.ub ;
        }

      and solve_member_binding_upd 
        (t : t) (x : AST.Prog.member_binding_upd_t) : 
          AST.Prog.member_binding_upd_t = 
        let eit, expr = x in
        (eit, solve_expr t expr)

      and solve_arglist 
        (t : t) (x : AST.Prog.arglist_t) : AST.Prog.arglist_t = 
        {
          positional = List.map 
            (fun x -> solve_expr t x) x.positional ; 
          named = List.map 
            (fun x -> let id, expr = x in 
              (id, solve_expr t expr)) x.named
        }
      
      and solve_seq_desplay 
        (t : t) (x : AST.Prog.seq_display_t) :
        AST.Prog.seq_display_t = 
        match x with 
        | SeqEnumerate exprs -> 
          SeqEnumerate
            (List.map (fun x -> solve_expr t x) exprs)
        | SeqTabulate x -> 
          SeqTabulate {
            gen_inst = x.gen_inst ;
            len = solve_expr t x.len ;
            func = solve_expr t x.func ;
          }
      
      and solve_quantification
        (t : t) (x : AST.Prog.quantification_t) :
        AST.Prog.quantification_t = 
        {
          qt = x.qt ;
          qdom = solve_qdom t x.qdom ;
          qbody = solve_expr t x.qbody ;
        }

      and solve_map_comp
        (t : t) (x : AST.Prog.map_comp_t) :
        AST.Prog.map_comp_t = 
        {
          imap = x.imap ; 
          qdom = solve_qdom t x.qdom ;
          key = solve_expr_option t x.key ;
          valu = solve_expr t x.valu ;
        }

      and solve_set_comp 
        (t : t) (x : AST.Prog.set_comp_t) :
        AST.Prog.set_comp_t = 
        {
          qdom = solve_qdom t x.qdom ;
          body = solve_expr_option t x.body ;
        }
      
      and solve_attribute 
        (t : t) (x : AST.Prog.attribute_t) =
        let s, exprs = x in
        (s, List.map (fun x -> solve_expr t x) exprs)
      
      and solve_case_expr
        (t : t) (x : AST.Prog.case_expr_t) :
        AST.Prog.case_expr_t = 
        match x with AST.Prog.Case (attrs, ext_pat, expr) ->
        Case (
          List.map 
            (fun x -> solve_attribute t x) attrs, 
          ext_pat, 
          solve_expr t expr
        )

      and solve_qvar_decl 
        (t : t) (x : AST.Prog.qvar_decl_t) :
        AST.Prog.qvar_decl_t = 
        match x with AST.Prog.QVar (id, tp, expro, attrs) ->
        AST.Prog.QVar (
          id, tp, 
          solve_expr_option t expro, 
          List.map 
            (fun x -> solve_attribute t x) attrs
        )

      and solve_qdom
        (t : t) (x : AST.Prog.qdom_t) : 
        AST.Prog.qdom_t = 
        match x with QDom x ->
        QDom {
          qvars = List.map (fun x -> solve_qvar_decl t x) x.qvars ;
          qrange = solve_expr_option t x.qrange ;
        }

      and solve_lhs 
        (t : t) (x : AST.Prog.lhs_t) : AST.Prog.lhs_t = 
        solve_expr t x 
      
      and solve_rhs 
        (t : t) (x : AST.Prog.rhs_t) : AST.Prog.rhs_t = 
        let expr, attrs = x in
        (
          solve_expr t expr, 
          List.map 
            (fun x -> solve_attribute t x) attrs
        )
      
      and solve_var_decl 
        (t : t) (x : AST.Prog.var_decl_t) : AST.Prog.var_decl_t = 
        match x with DeclIds (var_decl_id_lhss, var_decl_ids_rhs_o) ->
          DeclIds (
            List.map (fun x -> solve_var_decl_id_lhs t x)
              var_decl_id_lhss, 
            match var_decl_ids_rhs_o with 
            | None -> None 
            | Some x -> Some (solve_var_decl_ids_rhs_t t x)
          )

      and solve_var_decl_id_lhs 
        (t : t) (x : AST.Prog.var_decl_id_lhs_t) :
        AST.Prog.var_decl_id_lhs_t = 
        {
          id = x.id ;
          tp = x.tp ;
          attrs = List.map 
            (fun x -> solve_attribute t x) x.attrs ;
        }

      and solve_var_decl_ids_rhs_t
        (t : t) (x : AST.Prog.var_decl_ids_rhs_t) :
        AST.Prog.var_decl_ids_rhs_t = 
        match x with Assign rhss ->
          Assign (
            List.map (fun x -> solve_rhs t x) rhss
          )

    end
  
  end

  module API = struct 

    let construct_for_members
      (t : t)
      (members : AST.Prog.expr_t list) 
      : AST.Prog.expr_t list = 
      List.map 
      (
        fun member ->
          let sub_v = query_tracker_v_top_lvl t member in
          (construct sub_v)
      ) members

    let assign
      (t : t)
      (k : AST.Prog.expr_t)
      (v : AST.Prog.expr_t) : t = 
      let v' = Obligation.Prog.solve_expr t v in
      (* Note that here we might do not need a Obligation Solver at all *)
      (* TCommon.debug_print 
        ("[Tracker] assign " ^ 
        (TCommon.str_of_expr k) ^ " <- " ^ (TCommon.str_of_expr v)) ; *)
      if print_log then 
        TCommon.debug_print 
          ("[Tracker] assign " ^ 
          (TCommon.str_of_expr k) ^ " <- " ^ (TCommon.str_of_expr v)) ; 
      let t = assign t k v' in
      (* TCommon.debug_print (String.concat " - " (get_member_id_lst_from_t t)) ; *)
      t

    let build (fs : AST.TopDecl.formal_t list) : t =
      let empty_tracker_k = 
        AST.TopDecl.Formal 
          (false, "", TCommon.tp_of_id "") in
      let tracker_vs : tracker_v list = 
        List.map (
          fun (f : tracker_k) : tracker_v -> 
          {
            assigned_v = TCommon.expr_blank ;
            t = build f ;
          }
        ) fs in
      let tracker = Tracker (empty_tracker_k, tracker_vs) in
      let _ = 
      if print_tracker_built then 
        TCommon.debug_print 
        ("[Tracker] built " ^ (show tracker)) else () in

      tracker

    let saturation_check (t : t) : bool = 
      let rec aux (v : tracker_v) : bool =
        match TCommon.is_expr_n_blank v.assigned_v with
        | true -> true | false ->
          (* (
            match v.t with Tracker (k, _) ->
              match k with AST.TopDecl.Formal (_, _, _) ->
              TCommon.debug_print (id ^ " unfilled.") ;
          ) ; *)
          match v.t with Tracker (_, sub_vs) ->
          let check_args = List.for_all aux sub_vs in
          check_args && ((List.length sub_vs) <> 0 )
      in
      match t with Tracker(_, vs) ->
        List.for_all aux vs

    let compare
      (t1 : t) (t2 : t) : bool = compare t1 t2

    let merge
      (t1 : t) (t2 : t) : t = merge t1 t2

    let get_assigned_lst 
      (t : t) : AST.Prog.expr_t list = 
      get_assigned_lst [] t

    let rec clear (t : t) : t = 
      match t with Tracker (tracker_k, tracker_vs) ->
      match tracker_vs with 
      | [] -> t
      | _ -> 
        Tracker 
          (tracker_k, 
            List.map (
              fun x ->
                { assigned_v = TCommon.expr_blank ; 
                  t = clear x.t }
            ) tracker_vs)

  end

end
