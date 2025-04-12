open Internal

module Dafny = Syntax.ParserPass
module TLA = TlaSyntax.AST

let stub_str = "STUB"

(* Dafny Helper start *)

let type_filter (x : string) : string = 
  match x with 
  | "Int" -> "int" | _ -> x

let blank_str = 
  Dafny.Prog.NameSeg ("", []) 

let dafny_str_of_expr (e : Dafny.Prog.expr_t) : string = 
  match e with 
  | NameSeg name_seg -> begin
    let id, _ = name_seg in id
  end
  | _ -> assert false

let dafny_expr_of_str (x: string) : Dafny.Prog.expr_t = 
  Dafny.Prog.NameSeg (x, [])

let dafny_tp_of_str (x : string) : Dafny.Type.t = 
  let x = type_filter x in
  Dafny.Type.simple_generic x [] ()

let dafny_string_lst_to_dot_expr
  (lst : string list) : Dafny.Prog.expr_t = 
  let lst = List.map dafny_expr_of_str lst in
  let lst = NonEmptyList.coerce lst in
  NonEmptyList.fold_left_1 begin
    fun l r ->
      let r_id = dafny_str_of_expr r in
      Suffixed (
        l, 
        AugDot (DSId(r_id), [])
      )
  end lst

let chain_conjunct (exprs: Dafny.Prog.expr_t list) (op: Syntax.Common.bop_t): Dafny.Prog.expr_t =
  let rec aux exprs = 
    match exprs with
    | [] -> assert false
    | x :: [] -> x
    | x :: xs -> 
      let h = x in
      let rest = aux xs in
      Dafny.Prog.Binary ((), op, h, rest)
  in
  aux exprs 

(* Dafny Helper end *)

let str_of_general_id (id: TLA.general_identifier_t) : string =
  let _, id = id in id

let str_of_expr (x : TLA.expr_t) : string = 
  match x with 
  | TLA.Id id -> str_of_general_id id
  | _ -> assert false

let str_of_id_or_op_decl (x : TLA.id_or_op_decl_t) : string = 
  match x with 
  | Id id -> id
  | OpDecl op_decl -> (
    match op_decl with
    | NameOnly id -> id
    | _ -> assert false
  )

let str_of_argument (x : TLA.argument_t) : string = 
  match x with 
  | ArgExpr expr -> str_of_expr expr
  | _ -> assert false

let rec tp_of_expr(x : TLA.expr_t) : Dafny.Type.t = 
  match x with 
  | TLA.Id id -> dafny_tp_of_str (str_of_general_id id)
  | PrefixOp (op, expr) -> 
    let _, op = op in 
    (
      match op with 
      | SubsetPrefix -> 
        Dafny.Type.set (tp_of_expr expr) ()
      | _-> assert false
    ) 
  | FunctionCall (general_id, args) -> 
    let id = str_of_general_id general_id in
    (
      match id with 
      | "Seq" -> (
        let arg = NonEmptyList.head args in
        let arg_str = str_of_argument arg in
        let arg_tp = dafny_tp_of_str arg_str in
        let tp = Dafny.Type.seq arg_tp () in 
        tp
      )
      | _ -> assert false
    )
  | _ -> assert false

let str_of_operation_def_helper (helper: TLA.operator_definition_helper_t) : string = 
  match helper with 
  | NonFix non_fix_lhs -> 
    let id, _ = non_fix_lhs in id
  | _ -> assert false

let rec dot_expr_to_str_lst (x: TLA.expr_t) : string list = 
  match x with 
  | TLA.Id id -> [str_of_general_id id]
  | TLA.InfixOp (le, op, re) -> 
    let _, op = op in 
    (
      match op with 
      | Dot -> 
        let l_lst = dot_expr_to_str_lst le in
        let r_lst = dot_expr_to_str_lst re in
        l_lst @ r_lst
      | Lt -> ( 
        assert false;
       )
      | _ -> assert false
    )
  | _ -> assert false

let rec t_expr (x: TLA.expr_t) : Dafny.Prog.expr_t = 
  match x with 
  | Id id -> dafny_expr_of_str (str_of_general_id id)
  | FunctionCall (general_id, args) -> 
    let aux (x : TLA.argument_t) : Dafny.Prog.expr_t = 
      match x with 
      | ArgExpr expr -> t_expr expr
      | _ -> assert false
    in
    let id = str_of_general_id general_id in
    (
      match id with 
      | "Len" | "Cardinality" -> let sub_e = NonEmptyList.head args in let sub_e = aux sub_e in Dafny.Prog.Cardinality sub_e
      | "SubSeq" -> (
        let args = NonEmptyList.map aux args in
        let args = NonEmptyList.as_list args in
        let name, lb, rb = (match args with | [a; b; c] -> a, b, c | _ -> assert false) in
        Dafny.Prog.Suffixed (
          name, 
          Dafny.Prog.Subseq {lb=Some lb; ub=Some rb;}
        ) 
      )
      | _ -> 
        let args = NonEmptyList.as_list args in
        let arglist : Dafny.Prog.arglist_t = {
          positional = List.map aux args;
          named = [];
        } in
        Dafny.Prog.Suffixed(dafny_expr_of_str id, Dafny.Prog.ArgList (arglist, ()))
    )
  | PrefixOp (op, expr) -> 
    let _, op = op in 
    (
      match op with 
      | Domain -> t_expr expr
      | Not -> Dafny.Prog.Unary (Syntax.Common.Not, t_expr expr)
      | _ -> assert false
    )
  | InfixOp (le, op, re) -> 
    (
      let _, op = op in 
      match op with 
      | Dot -> 
        (
          match le with 
          | FunctionApplication _ -> (
            let le' = t_expr le in
            let re_str_lst = dot_expr_to_str_lst re in
            let rec aux lst res = 
              match lst with 
              | [] -> res
              | h :: rest ->
                let res = Dafny.Prog.Suffixed (
                  res, 
                  AugDot (DSId(h), [])
                ) in
                aux rest res
            in
            aux re_str_lst le'
          )
          | _ -> ( let dot_str_lst = dot_expr_to_str_lst x in dafny_string_lst_to_dot_expr dot_str_lst )
        )
      | Lt -> Dafny.Prog.Binary ((), Syntax.Common.Lt, t_expr le, t_expr re)
      | Le -> Dafny.Prog.Binary ((), Syntax.Common.Lte, t_expr le, t_expr re)
      | Eq -> (
        match re with 
        | StringLiteral str -> 
          let dot_str_lst = dot_expr_to_str_lst le in
          let dot_str_lst = dot_str_lst @ [str ^ "?"] in
          let expr = dafny_string_lst_to_dot_expr dot_str_lst in
          expr
        | _ ->
          Dafny.Prog.Binary ((), Syntax.Common.Eq, t_expr le, t_expr re)
      )
      | Neq -> (
        match re with 
        | StringLiteral str -> 
          let dot_str_lst = dot_expr_to_str_lst le in
          let dot_str_lst = dot_str_lst @ [str ^ "?"] in
          let expr = dafny_string_lst_to_dot_expr dot_str_lst in
          expr
        | _ ->
          Dafny.Prog.Binary ((), Syntax.Common.Neq, t_expr le, t_expr re)
      )
      | Ge -> Dafny.Prog.Binary ((), Syntax.Common.Gte, t_expr le, t_expr re)
      | Gt -> Dafny.Prog.Binary ((), Syntax.Common.Gt, t_expr le, t_expr re)
      | And -> Dafny.Prog.Binary ((), Syntax.Common.And, t_expr le, t_expr re)
      | Or -> Dafny.Prog.Binary ((), Syntax.Common.Or, t_expr le, t_expr re)
      | UnionInfix -> Dafny.Prog.Binary ((), Syntax.Common.Add, t_expr le, t_expr re)
      | Concat -> Dafny.Prog.Binary ((), Syntax.Common.Add, t_expr le, t_expr re)
      | Plus -> Dafny.Prog.Binary ((), Syntax.Common.Add, t_expr le, t_expr re)
      | Minus -> Dafny.Prog.Binary ((), Syntax.Common.Sub, t_expr le, t_expr re)
      | Div -> Dafny.Prog.Binary ((), Syntax.Common.Div, t_expr le, t_expr re)
      | Implies -> Dafny.Prog.Binary((), Syntax.Common.Implies, t_expr le, t_expr re)
      | In -> Dafny.Prog.Binary((), Syntax.Common.In, t_expr le, t_expr re)
      | NotIn -> Dafny.Prog.Binary((), Syntax.Common.Nin, t_expr le, t_expr re)
      | _ -> assert false
    )
  | Parenthesized expr -> t_expr expr
  | QuantifierWithoutBound (qtf, ids, expr) ->
    let ids = NonEmptyList.as_list ids in
    let aux (x: string) : Dafny.Prog.qvar_decl_t = 
      Dafny.Prog.QVar (x, None, None, [])
    in
    Dafny.Prog.Quantifier (
      (), 
      {
        qt = (match qtf with | ForAll -> Syntax.Common.Forall | Exists -> Syntax.Common.Exists | _ -> assert false);
        qdom = Dafny.Prog.QDom { qvars = List.map aux ids; qrange = None; };
        qbody = t_expr expr;
      }
    )
  | ExplicitSet exprs -> 
    let exprs' = (match exprs with | Some exprs -> NonEmptyList.as_list exprs | None -> []) in
    let exprs' = List.map t_expr exprs' in
    Dafny.Prog.SetDisplay exprs'
  | FunctionApplication (expr, args) -> 
    let arg = NonEmptyList.head args in
    let arg = t_expr arg in
    let expr = t_expr expr in
    Dafny.Prog.Suffixed(expr, Dafny.Prog.Sel arg)
  | RecordConstructor args ->
    let aux x : Dafny.Prog.expr_t = 
      let _, x = x in t_expr x
    in
    let args = NonEmptyList.as_list args in 
    let arglist : Dafny.Prog.arglist_t = {
      positional = List.map aux args;
      named = [];
    } in
    Dafny.Prog.Suffixed(dafny_expr_of_str stub_str, Dafny.Prog.ArgList (arglist, ()))
  | FunctionUpdate (updated_base, updates) -> 
    let aux1 (x : TLA.function_update_helper_t NonEmptyList.t) : string = 
      let h = NonEmptyList.head x in
      match h with 
      | UpdateName id -> id | _ -> assert false
    in
    let aux2 (x : (TLA.function_update_helper_t NonEmptyList.t * TLA.expr_t)) : Dafny.Prog.member_binding_upd_t = 
      let helpers, assigned = x in
      let name = aux1 helpers in
      (Either.left name, t_expr assigned)
    in
    let updates = NonEmptyList.map aux2 updates in
    let suffix = Dafny.Prog.DataUpd ((), updates) in
    Dafny.Prog.Suffixed(t_expr updated_base, suffix)
  | TupleExpr exprs ->
    let exprs' = NonEmptyList.as_list exprs in
    let exprs' = List.map t_expr exprs' in
    Dafny.Prog.SeqDisplay (
      Dafny.Prog.SeqEnumerate exprs'
    )
  | IfThenElseExpr (e1, e2, e3) ->
    let e1' = t_expr e1 in
    let e2' = t_expr e2 in
    let e3' = t_expr e3 in
    Dafny.Prog.If ((), e1', e2', e3')
  | LetInExpr (helpers, body) ->
    (
      let helper = NonEmptyList.head helpers in
      match helper with
      | LetOperatorDefinition (def_helper, expr) -> 
        let def_helper_str = str_of_operation_def_helper def_helper in
        let expr' = t_expr expr in
        let pats = NonEmptyList.coerce [Dafny.Prog.PatVar (def_helper_str, None)] in
        let defs = NonEmptyList.coerce [expr'] in
        let body = t_expr body in
        Dafny.Prog.Let {ghost=false; pats=pats; defs=defs; body=body}
      | _ -> assert false
    )
  | ConjunctionChain exprs -> 
    let exprs' = NonEmptyList.as_list exprs in
    let exprs' = List.map t_expr exprs' in
    chain_conjunct exprs' Syntax.Common.And
  | DisjunctionChain exprs ->
    let exprs' = NonEmptyList.as_list exprs in
    let exprs' = List.map t_expr exprs' in
    chain_conjunct exprs' Syntax.Common.Or
  | NumberLiteral num -> Dafny.Prog.Lit (Syntax.Common.Nat num)
  | StringLiteral str -> Dafny.Prog.Lit (Syntax.Common.String str)
  | EmptyTuple -> 
    Dafny.Prog.SeqDisplay (
      Dafny.Prog.SeqEnumerate []
    )
  | EmptyRecord -> (
      Dafny.Prog.Suffixed(dafny_expr_of_str "map", Dafny.Prog.Sel blank_str)
    )
  | _ -> assert false

let t_unit (unit: TLA.unit_t) : Dafny.TopDecl.t = 
  match unit with 
  | OperatorDefinition operator_def_t -> 
    let (def_helper, expr) = operator_def_t in
    let non_fix_lhs = (match def_helper with | NonFix x -> x | _ -> assert false) in
    let id_lhs, args = non_fix_lhs in
    (
    match args with
    | Some args -> 
      (
        let args = NonEmptyList.as_list args in
        let args = List.map str_of_id_or_op_decl args in
        let aux (id : string) : Dafny.TopDecl.formal_t = 
          let tp = dafny_tp_of_str stub_str in
          Dafny.TopDecl.Formal (false, id, tp)
        in
        let formals = List.map aux args in
        let expr' = t_expr expr in
        let f = 
          Dafny.TopDecl.Predicate (
            (), false, [], id_lhs, [], formals, [], expr'
          ) in
        [], Dafny.TopDecl.PredFunDecl f
      )
    | None -> (
      let def_helper_str = id_lhs in
      match expr with
      | Id general_id -> 
        let general_id_str = str_of_general_id general_id in
        let tp = dafny_tp_of_str general_id_str in
        let synonym_type: Dafny.TopDecl.synonym_type_t = {
          ann = (); attrs = []; id = def_helper_str; params = []; 
          rhs = Dafny.TopDecl.Synonym tp;
        } in
        [], Dafny.TopDecl.SynonymTypeDecl synonym_type
      | FunctionCall (general_id, args) -> 
        let id = str_of_general_id general_id in
        (
          match id with 
          | "Seq" -> (
            let arg = NonEmptyList.head args in
            let arg_str = str_of_argument arg in
            let arg_tp = dafny_tp_of_str arg_str in
            let tp = Dafny.Type.seq arg_tp () in 
            let synonym_type: Dafny.TopDecl.synonym_type_t = {
              ann = (); attrs = []; id = def_helper_str; params = []; 
              rhs = Dafny.TopDecl.Synonym tp;
            } in
            [], Dafny.TopDecl.SynonymTypeDecl synonym_type
          )
          | _ ->
            let arg = NonEmptyList.head args in
            let arg_str = str_of_argument arg in
            let arg_tp = dafny_tp_of_str arg_str in
            let tp = Dafny.Type.simple_generic id [arg_tp] () in 
            let synonym_type: Dafny.TopDecl.synonym_type_t = {
              ann = (); attrs = []; id = def_helper_str; params = []; 
              rhs = Dafny.TopDecl.Synonym tp;
            } in
            [], Dafny.TopDecl.SynonymTypeDecl synonym_type
        )
      | RecordTypeAnnotation annos -> 
        let aux x = 
          let name, expr = x in 
          let tp = tp_of_expr expr in
          Dafny.TopDecl.Formal (false, name, tp)
        in
        let annos = NonEmptyList.as_list annos in
        let ctor = Dafny.TopDecl.DataCtor (
          [], def_helper_str, (List.map aux annos)
        ) in
        [], Dafny.TopDecl.DatatypeDecl ((), [], def_helper_str, [], NonEmptyList.coerce [ctor])
      | SimpleMapping (k, y) -> 
        let k_str = str_of_expr k in
        let y_str = str_of_expr y in
        let tp_k = dafny_tp_of_str k_str in
        let tp_y = dafny_tp_of_str y_str in
        let tp = Dafny.Type.map tp_k tp_y () in 
        let synonym_type: Dafny.TopDecl.synonym_type_t = {
          ann = (); attrs = []; id = def_helper_str; params = []; 
          rhs = Dafny.TopDecl.Synonym tp;
        } in
        [], Dafny.TopDecl.SynonymTypeDecl synonym_type
      | _ -> assert false
    )
    )
    | _ -> assert false

let translate (tla_module: TlaSyntax.AST.module_t) : Dafny.t =
  let _module_name, _extends, units = tla_module in
    let units' = List.map t_unit units in 
    Dafny { includes=[]; decls=units' }
