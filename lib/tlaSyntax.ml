open Internal

module AST = struct 

  type 'a comma_list_t = 'a NonEmptyList.t

  type name_t = string
  type id_t = string
  type id_or_tuple_t = 
    | Id of id_t
    | Tuple of id_t comma_list_t (* << ... ... >> *)
  type number_t = int
  type string_t = string

  type prefix_op_t =
  | Neg           (* "-" — arithmetic negation *)
  | Not           (* "~" | "\\lnot" | "\\neg" | "\\not" — logical NOT *)
  | Always        (* "[]" — temporal 'always' (□) *)
  | Eventually    (* "<>" — temporal 'eventually' (◇) *)
  | Domain        (* "DOMAIN" — function domain extraction *)
  | Enabled       (* "ENABLED" — action enabledness predicate *)
  | SubsetPrefix  (* "SUBSET" — powerset operator *)
  | Unchanged     (* "UNCHANGED" — state unchanged predicate *)
  | UnionPrefix   (* "UNION" — generalized union (⋃ over set of sets) *)

  (**
    Some definition in the reference 
    (* https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/Syntax/TLAPlusGrammar.tla *)
    are skipped here, because they are not used in the standard TLA+ grammar.
    '''
    !!    #     ##    $     $$     %     %%    
    &     &&    (+)   (-)   (.)    (/)   (\X)
    **    ++    -+->  --    -|     ..    ...
    //    ::=   :=    :>    <:     =|    ?
    ??    @@    |     |-    |=     ||    ~>    .
    '''
  *)
  type infix_op_t =
  (* Arithmetic *)
  | Plus        (* "+" — addition *)
  | Minus       (* "-" — subtraction *)
  | Times       (* "*" — multiplication *)
  | Div         (* "/" — division *)
  | Exp         (* "^" | "**" — exponentiation *)

  (* Comparison *)
  | Eq          (* "=" — equality *)
  | Neq         (* "/=" — inequality *)
  | Lt          (* "<" — less than *)
  | Le          (* "<=" | "=<" | "\\leq" — less than or equal *)
  | Gt          (* ">" — greater than *)
  | Ge          (* ">=" | "\\geq" — greater than or equal *)

  (* Set operations *)
  | NotIn
  | In          (* "\\in" — set membership *)
  | SubsetInfix (* "\\subset" — proper subset *)
  | SubsetEq    (* "\\subseteq" — subset or equal *)
  | UnionInfix  (* "\\cup" | "\\union" — set union *)
  | Intersect   (* "\\cap" | "\\intersect" — set intersection *)
  | SetMinus    (* "\\" — set difference *)

  (* Sequence / function *)
  | Concat      (* "^^" | "@" | "\\o" — sequence concatenation *)
  | MapTo       (* "|->" | ":>" — function mapping *)

  (* Logic *)
  | And         (* "/\\" | "\\land" — logical and *)
  | Or          (* "\\/" | "\\lor" — logical or *)
  | Implies     (* "=>" — implication *)
  | Equiv       (* "<=>" | "\\equiv" — logical equivalence *)

  | Dot        (* "." — dot operator, used in record access and function application *)

  type postfix_op_t =
  | PlusClosure     (* "^+" — transitive closure (e.g., relation^+) *)
  | StarClosure     (* "^*" — reflexive-transitive closure (e.g., relation^* ) *)
  | Cardinality     (* "^#" — cardinality operator, used with sets/sequences *)
  | Prime           (* "'"  — next-state operator in action formulas *)

  type module_t = 
    name_t * (name_t comma_list_t) option * unit_t list

  and unit_t =
    | VariableDeclaration of variable_declaration_t
    | ConstantDeclaration of constant_declaration_t 
    | OperatorDefinition of operator_definition_t
    | FunctionDefinition of function_definition_t
    | Instance of instance_t
    | ModuleDefinition of module_definition_t
    | Assumption of assumption_t
    | Theorem of therom_t
    | Module of module_t
    | AtLeast4Minus

  and variable_declaration_t = id_t comma_list_t

  and constant_declaration_t = op_decl_t comma_list_t

  and op_decl_t =
    | NameOnly of id_t
    | FunctionWithUnderscores of id_t
    | PrefixOpDecl of prefix_op_t
    | InfixOpDecl of infix_op_t
    | PostfixOpDecl of postfix_op_t

  and operator_definition_helper_t =
    | NonFix of non_fix_lhs_t
    | PrefixForm of prefix_op_t * id_t
    | InfixForm of id_t * infix_op_t * id_t
    | PostfixForm of id_t * postfix_op_t
  
  and operator_definition_t = operator_definition_helper_t * expr_t

  and id_or_op_decl_t = 
    | Id of id_t
    | OpDecl of op_decl_t

  and non_fix_lhs_t = 
    id_t * (id_or_op_decl_t comma_list_t option)
    
  and function_definition_t = id_t * quantifier_bound_t comma_list_t * expr_t

  and quantifier_bound_helper_t = 
    | QtfierBoundIdOrTuple of id_or_tuple_t
    | QtfierBoundIdList of id_t comma_list_t

  and quantifier_bound_t = quantifier_bound_helper_t * expr_t

  and instance_t = name_t * substitution_t comma_list_t

  and substitution_helper_t = 
    | SubstId of id_t
    | SubstPrefix of prefix_op_t
    | SubstInfix of infix_op_t
    | SubstPostfix of postfix_op_t
  
  and substitution_t = substitution_helper_t * argument_t

  and argument_t = 
    | ArgExpr of expr_t
    | ArgPrefix of general_prefix_op_t
    | ArgInfix of general_infix_op_t
    | ArgPostfix of general_postfix_op_t

  and instance_prefix_t =
    (id_t * expr_t comma_list_t option) list

  and general_identifier_t = instance_prefix_t * id_t
  and general_prefix_op_t = instance_prefix_t * prefix_op_t
  and general_infix_op_t = instance_prefix_t * infix_op_t
  and general_postfix_op_t = instance_prefix_t * postfix_op_t

  and module_definition_t = non_fix_lhs_t * instance_t

  and assumption_t = expr_t

  and therom_t = expr_t

  and quantifier_t = | ForAll | Exists | ActionForAll | ActionExists

  and function_update_helper_t = 
    | UpdateName of name_t
    | UpdateExprs of expr_t comma_list_t

  and fairness_t = | Sf | Wf

  and let_in_helper_t = 
    | LetOperatorDefinition of operator_definition_t
    | LetFunctionDefinition of function_definition_t
    | LetModuleDefinition of module_definition_t

  and expr_t = 
    | Id of general_identifier_t
    | FunctionCall of general_identifier_t * argument_t comma_list_t 
    | PrefixOp of general_prefix_op_t * expr_t 
    | InfixOp of expr_t * general_infix_op_t * expr_t 
    | PostfixOp of expr_t * general_postfix_op_t 
    | Parenthesized of expr_t 
    | QuantifierWithBound of quantifier_t * quantifier_bound_t comma_list_t * expr_t
    | QuantifierWithoutBound of quantifier_t * id_t comma_list_t * expr_t
    | Choose of id_or_tuple_t * expr_t option * expr_t
    | ExplicitSet of expr_t comma_list_t option
    | SetComprehension of id_or_tuple_t * expr_t * expr_t
    | SetConstructor of expr_t * quantifier_bound_t comma_list_t
    | FunctionApplication of expr_t * expr_t comma_list_t
    | FunctionConstructor of quantifier_bound_t comma_list_t * expr_t
    | SimpleMapping of expr_t * expr_t
    | RecordConstructor of (name_t * expr_t) comma_list_t
    | RecordTypeAnnotation of (name_t * expr_t) comma_list_t
    | FunctionUpdate of expr_t * (function_update_helper_t NonEmptyList.t * expr_t) comma_list_t
    | TupleExpr of expr_t comma_list_t
    | CartesianProductExpr of expr_t * expr_t NonEmptyList.t
    | BoxActionExpr of expr_t * expr_t
    | DiamondActionExpr of expr_t * expr_t
    | FairnessExpr of fairness_t * expr_t * expr_t
    | IfThenElseExpr of expr_t * expr_t * expr_t
    | CaseExpr of expr_t * expr_t * (expr_t * expr_t) list * expr_t option
    | LetInExpr of let_in_helper_t NonEmptyList.t * expr_t
    | ConjunctionChain of expr_t NonEmptyList.t
    | DisjunctionChain of expr_t NonEmptyList.t
    | NumberLiteral of number_t
    | StringLiteral of string_t
    | AtSymbol
    | EmptyTuple (* Not in the BNF but used in the Paxos Spec *)
    | EmptyRecord (* Not in the BNF but used in the Paxos Spec *)
    (* | DotHelper of id_t list * expr_t A tmp helper for parsing, should be removed later *)

end
