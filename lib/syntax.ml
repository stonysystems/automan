(** Abstract syntax. *)

module type MetaData = sig
  (* Use [@opaque] for instances where we don't want to / can't print this *)
  type predicate_t [@@deriving show]
end

module TrivMetaData : MetaData
  with type predicate_t = unit
= struct
  type predicate_t = unit [@@deriving show]
end

type id   = string
[@@deriving show]

module AST (M : MetaData) = struct
  type tp =
    | TpId  of id * tp list
    | TpTup of tp list
  [@@deriving show]

  type arith =
    | Add           of expr * expr
    | Sub           of expr * expr
    | Mult          of expr * expr
    | Div           of expr * expr
    | Mod           of expr * expr

  and boolean =
    | And           of expr * expr
    | Or            of expr * expr

  and cmp = 
    | Eq            of expr * expr
    | Neq           of expr * expr
    | Lt            of expr * expr
    | Lte           of expr * expr
    | Gt            of expr * expr
    | Gte           of expr * expr
    | In            of expr * expr
    | NotIn         of expr * expr

  and expr_implies = 
    (* expr <==> expr *)
    | ImpliesBoth   of expr * expr

    (* expr ==> expr *)
    | ImpliesL      of expr * expr

    (* expr <== expr *)
    | ImpliesR      of expr * expr

  and q_var = 
  (*
    * forall QVar :: expr
    * exists QVar :: expr    
    *)
    | QVar          of expr list

  and expr_qtfier = 
    | QForall       of q_var * expr list * expr
    | QExists       of q_var * expr

  and expr_bin_op = 
    | Arith         of arith
    | Bool          of boolean
    | Cmp           of cmp
    (* expr.expr *)
    | Attribute     of expr * expr
  (*
    * expr.(iassign, iassign, ... )
    * x.(a := 1, b := 2)
    *)
    | AUpdate       of expr * iassign list

  and map_ctor = 
  (*
    * { iassign, iassign, ... ... }
    * { 1 := 1, x := 2 }
    *)
    | MapCtorSpec   of iassign list
  (*
    * map expr | expr :: expr    
    * map opn | opn in votes && opn >= log_truncation_point :: votes[opn]
    *)
    | MapCtorItor   of expr * expr * expr

  and seq_ctor = 
  (*
    * [expr, expr, expr ... ...]    
    *)
    | SeqCtorSpec   of expr list
  (*
    * seq(expr, expr => expr)
    * seq(|c.all.config.replica_ids|, idx => 0)
    *)
    | SeqCtorItor   of expr * expr * expr

  and set_ctor =
  (*
    * { expr, expr, expr }
    * { 1, 2, x, a + b   }
    *)
    | SetCtorSpec   of expr list
    | SetCtorItor   of expr * expr
    | SetCtorItorSuchThat
      of id list * expr * expr

  and expr_coll_ctor = 
    | MapCtor       of map_ctor
    | SeqCtor       of seq_ctor
    | SetCtor       of set_ctor

  and expr_slice = 
    (* ..expr *)
    | SliceNoL      of expr
    (* expr.. *)
    | SliceNoR      of expr
    (* expr..expr *)
    | SliceLR       of expr * expr

  and iassign = 
    (* expr := expr *)
    | IAssign       of expr * expr

  and assigned =
    (* (id, id, id) *)
    | AssignedTpl   of id list
    (* id *)
    | AssignedId    of id

  and stmt = 
  (*
    * (id, id, id) := expr
    * id := expr  
    *)
    | StmtAssign    of assigned * expr

  (*
    * var (id, id, id) := expr
    * var id := expr 
    *)
    | StmtVAssign   of assigned * expr

  (*
    * assert expr ; 
    *)
    | StmtAssert    of expr

  (*
    * id(expr, expr, expr);
    *)
    | StmtCall      of id * expr list

  (*
    * { stmt; stmt; stmt; }
    *)
    | StmtsBraced   of stmt list

  (*
    * if expr {stmt}  
    *)
    | StmtIf        of expr * stmt

  (*
    * StmtIf else {stmt}  
    * if x { ... } -> StmtIf |  else { ... } -> Stmt
      StmtIfElse = Stmt(StmtIf) * Stmt
                  = Stmt * Stmt
    *)
    | StmtIfElse    of stmt * stmt 

    (* StmtIfElse {stmt} *)
    | StmtIfElif    of stmt * stmt


  and case = 
    | Case          of expr * expr

  and expr = 
    (* id(expr, expr, expr) *)
    | ExprCall      of id * expr list

    (*  This is the same as the iassign defined above
      * This is a tempral solution for a grammar conflict
      * Can be removed later
    *)
    | ExprIAssignForCall 
      of expr * expr

    (* id *)
    | ExprId        of id

    (* 1 *)
    | ExprInt       of int

    (* ( expr ) *)
    | PExpr         of expr

    | ExprBinOp     of expr_bin_op

    (* expr[expr] *)
    | ExprScpt      of expr * expr

    (* if expr then expr else expr *)
    | ExprIf        of expr * expr * expr

    (* | expr | *)
    | ExprLen       of expr

    | ExprCollCtor  of expr_coll_ctor

    (* a.b.c ? *)
    | ExprQuestionM of expr

    (* StmtVAssign; expr | var x := 1; expr *)
    | ExprLetBind   of stmt * expr

    (* expr[expr := expr, expr := expr, ...] *)
    | ExprCollAUpdate  
      of expr * iassign list
    | ExprImplies   of expr_implies
    | ExprQtfier    of expr_qtfier
    (* (expr, expr, expr) *)
    | ExprTuple     of expr list
    (* ! expr *)
    | ExprNot       of expr
    | ExprSlice     of expr_slice (* s[1..2] *)
    | ExprMatch     of expr * case list
    | ExprBlank

  and formal = 
    (* x : tp *)
    | Formal        of id * tp 

  and datatype_ctor = 
    (* X(a : tp, b : tp) *)
    | DatatypeCtor  of id * formal list

  and ctst = 
    | Requires      of expr
    | Ensures       of expr
    | Decreases     of expr

  and module_item = 
    | Import        of id
    | DatatypeDef   of id * datatype_ctor list
    | Predicate     of M.predicate_t * id * formal list * ctst list * expr
    | Function      of id * formal list * tp * ctst list * expr
    | FuncMethod    of id * formal list * tp * ctst list * expr
    | Method        of id * formal list * tp * ctst list * stmt list
    | Lemma         of id * formal list * ctst list * stmt list
    | Alias         of id * tp

  and module_items = module_item list

  and file_level = 
    | Include       of id
    | Module        of id * module_items
  [@@deriving show]
end

module ParserPass = AST (TrivMetaData)
