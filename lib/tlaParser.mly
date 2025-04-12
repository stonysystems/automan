%{
open Internal
open TlaSyntax.AST
%}

%right DOUBLEEQ              /* == */

%right NOT                   /* ~, ¬ */
%right DOMAIN SUBSET         /* DOMAIN f, SUBSET S, UNION S */

%left OR AND
%right IMPLIES

%nonassoc EQ NEQ
%nonassoc LT LE GT GE IN NOTIN

%left PLUS NEG UNION_SYM CONCAT
%left DIV

%left LBRACK

%left DOT

%start tla_module
%type <TlaSyntax.AST.module_t> tla_module

%%

nonempty_list_separated_by(T, S):
  | T { NonEmptyList.coerce [ $1 ] }
  | head = T; S; rest = nonempty_list_separated_by(T, S)
    { let rest_list = NonEmptyList.as_list rest in
      NonEmptyList.coerce (head :: rest_list) }

nonempty_list(T):
  | T { NonEmptyList.coerce [ $1 ] }
  | head = T; rest = nonempty_list(T) { let rest_list = NonEmptyList.as_list rest in
      NonEmptyList.coerce (head :: rest_list) }

id_or_tuple:
  | ID { Id $1 } // never reduced when paired with comma list ID
  | TUPLE_START; nonempty_list_separated_by(ID, COMMA); TUPLE_END { Tuple $2 }

prefix_op:
  | NEG { Neg }
  | NOT { Not }
  | ALWAYS { Always }
  | EVENTUALLY { Eventually }
  | DOMAIN { Domain }
  | ENABLED { Enabled }
  | SUBSET { SubsetPrefix }
  | UNCHANGED { Unchanged }
  | UNION { UnionPrefix }

infix_op:
  | DOT { Dot } 
  | PLUS { Plus }
  | NEG { Minus }
  | TIMES { Times }
  | DIV { Div }
  | EXP { Exp }
  | EQ { Eq }
  | NEQ { Neq }
  | LT { Lt }
  | LE { Le }
  | GT { Gt }
  | GE { Ge }
  | IN { In }
  | NOTIN { NotIn } /* Not in the original BNF but used in the PAXOS spec */
  | SUBSET_P { SubsetInfix }
  | SUBSETEQ { SubsetEq }
  | UNION_SYM { UnionInfix }
  | INTERSECT { Intersect }
  | SETMINUS { SetMinus }
  | CONCAT { Concat }
  | MAPTO { MapTo }
  | AND { And } 
  | OR { Or } 
  | IMPLIES { Implies }
  | EQUIV { Equiv }

postfix_op:
  | PLUSCLOSURE { PlusClosure }
  | STARCLOSURE { StarClosure }
  | CARDINALITY { Cardinality }
  | PRIME { Prime }

tla_module:
  MINUS4PLUS MODULE; name = ID; MINUS4PLUS;
  extends = option(extends);
  units = list(unit);
  EQ4PLUS; EOF;
  { (name, extends, units) }

extends:
  | EXTENDS; nonempty_list_separated_by(ID, COMMA) { $2 }

unit:
  // | variable_declaration { VariableDeclaration $1 }
  // | constant_declaration { ConstantDeclaration $1 }
  | option(LOCAL); operator_definition { OperatorDefinition $2 }
  // | option(LOCAL); function_definition { FunctionDefinition $2 }
  // | option(LOCAL); instance { Instance $2}
  // | option(LOCAL); module_definition { ModuleDefinition $2 }
  // | assumption { Assumption $1 }
  // | theorem { Theorem $1 }
  // | tla_module { Module $1 }
  // | MINUS4PLUS { AtLeast4Minus }

variable_declaration:
  | VARIABLE  ; nonempty_list_separated_by(ID, COMMA) { $2 }
  | VARIABLES ; nonempty_list_separated_by(ID, COMMA) { $2 }

constant_declaration:
  | CONSTANT ; nonempty_list_separated_by(op_decl, COMMA) { $2 }
  | CONSTANTS; nonempty_list_separated_by(op_decl, COMMA) { $2 }

op_decl:
  | ID { NameOnly $1 }
  | ID; LPAREN; nonempty_list_separated_by(UNDERSCORE, COMMA); RPAREN { FunctionWithUnderscores $1 }
  | prefix_op; UNDERSCORE { PrefixOpDecl $1 }
  | UNDERSCORE; infix_op; UNDERSCORE { InfixOpDecl $2 }
  | UNDERSCORE; postfix_op { PostfixOpDecl $2 }

operator_definition_helper:
  | non_fix_lhs { NonFix $1 } 
  // | prefix_op; ID { PrefixForm ($1, $2) }
  // | ID; infix_op; ID { InfixForm ($1, $2, $3) }
  // | ID; postfix_op { PostfixForm ($1, $2) }

operator_definition:
  | operator_definition_helper; DOUBLEEQ; expr { ($1, $3) }

// Note that "Identifier"is alreay defined in OpDecl, we dont really need id_or_op_decl
// ID here is never reduced
id_or_op_decl:
  | ID { Id $1 }
  | op_decl { OpDecl $1 }

non_fix_lhs_helper:
  | LPAREN; nonempty_list_separated_by(id_or_op_decl, COMMA); RPAREN { $2 }

non_fix_lhs:
  | ID; option(non_fix_lhs_helper) { ($1, $2) }

function_definition:
  | ID; LBRACK; nonempty_list_separated_by(quantifier_bound, COMMA); RBRACK; DOUBLEEQ; expr { ($1, $3, $6) }

quantifier_bound_helper:
  | id_or_tuple { QtfierBoundIdOrTuple $1 }
  | nonempty_list_separated_by(ID, COMMA) { QtfierBoundIdList $1 }

quantifier_bound:
  | quantifier_bound_helper; IN; expr { ($1, $3) }

instance:
  | INSTANCE; ID; option(WITH); nonempty_list_separated_by(substitution, COMMA) { ($2, $4) }

substitution_helper:
  | ID { SubstId $1 }
  | prefix_op { SubstPrefix $1 }
  | infix_op { SubstInfix $1 }
  | postfix_op { SubstPostfix $1 }

substitution:
  | substitution_helper; LARROW; argument { ($1, $3) }

argument:
  | expr { ArgExpr $1 }
  | general_prefix_op { ArgPrefix $1 } 
  | general_infix_op { ArgInfix $1 }
  | general_postfix_op { ArgPostfix $1 }

instance_prefix_helper_1:
  | LBRACE; nonempty_list_separated_by(expr, COMMA); RBRACE { $2 }

instance_prefix_helper_2:
  | ID; option(instance_prefix_helper_1); EXCLAMATION { ($1, $2) }

instance_prefix:
  | nonempty_list(instance_prefix_helper_2) { NonEmptyList.as_list $1 }

general_identifier:
  | instance_prefix; ID { ($1, $2) }
  | ID { ([], $1) }

general_prefix_op:
  | instance_prefix; prefix_op { ($1, $2) }
  | prefix_op { ([], $1) }

general_infix_op:
  // | instance_prefix; infix_op { ($1, $2) } // FIXME: "OperationNumber == Int" * 2
  | infix_op { ([], $1) }

general_postfix_op:
  | instance_prefix; postfix_op { ($1, $2) }
  | postfix_op { ([], $1) }

module_definition:
  | non_fix_lhs; DOUBLEEQ; instance { ($1, $3) }

assumption_helper:
  | ASSUME | ASSUMPTION | AXIOM { $1 }

assumption:
  | assumption_helper; expr { $2 }

theorem:
  | THEOREM; expr { $2 }

quantifier:
  | FORALL { ForAll } | EXISTS { Exists }
  | ACTION_FORALL { ActionForAll } | ACTION_EXISTS { ActionExists }

choose_helper:
  | IN; expr { $2 }

record_constructor_helper:
  | ID; MAPTO; expr { ($1, $3) }

record_type_annotation_helper:
  | ID; COLON; expr { ($1, $3) }

function_update_helper_1:
  | DOT; ID; { UpdateName $2 }
  | LBRACK; nonempty_list_separated_by(expr, COMMA); RBRACK { UpdateExprs $2 }

function_update_helper_2:
  | function_update_helper_1 { [ $1 ] }
  | function_update_helper_1; function_update_helper_2 { $1 :: $2 }

function_update_helper_3:
  | EXCLAMATION; function_update_helper_2; EQ; expr { (NonEmptyList.coerce $2, $4) }

cart_product_expr_helper:
  | CROSS; expr { [ $2 ] }
  | expr; cart_product_expr_helper { $1 :: $2 }

fairness_expr_helper:
  | SF_ { Sf }
  | WF_ { Wf }

case_arm:
  | expr; DARROW; expr { ($1, $3) }

case_arms:
  | case_arm { [ ] }
  | case_arm; case_arms { $1 :: $2 }

case_helper_1:
  | case_arm; LBRACK; RBRACK; case_arms { ($1, $4) }

case_helper_2:
  | LBRACK; RBRACK; OTHER; DARROW; expr { $5 }

let_in_expr_helper:
  | operator_definition { LetOperatorDefinition $1 }
  // | function_definition { LetFunctionDefinition $1 }
  // | module_definition   { LetModuleDefinition $1   }

conjunc_chain_helper:
  | AND; expr { $2 }

disconjunct_chain_helper:
  | OR; expr  { $2 }

infix_op_helper:
  // | expr; general_infix_op; expr { InfixOp ($1, $2, $3) }
  | expr; DOT; expr { InfixOp ($1, ([], Dot), $3) }

  | expr; LT; expr { InfixOp ($1, ([], Lt), $3) }
  | expr; LE; expr { InfixOp ($1, ([], Le), $3) }
  | expr; GT; expr { InfixOp ($1, ([], Gt), $3) }
  | expr; GE; expr { InfixOp ($1, ([], Ge), $3) }
  | expr; IN; expr { InfixOp ($1, ([], In), $3) }
  | expr; NOTIN; expr { InfixOp ($1, ([], NotIn), $3) } /* Not in the original BNF but used in the PAXOS spec */
  | expr; EQ; expr { InfixOp ($1, ([], Eq), $3) }
  | expr; NEQ; expr { InfixOp ($1, ([], Neq), $3) }

  | expr; UNION_SYM; expr { InfixOp ($1, ([], UnionInfix), $3) }
  | expr; CONCAT; expr  { InfixOp ($1, ([], Concat), $3) }
  | expr; PLUS; expr { InfixOp ($1, ([], Plus), $3) }
  | expr; NEG; expr { InfixOp ($1, ([], Minus), $3) }
  | expr; DIV; expr { InfixOp ($1, ([], Div), $3) }
  | expr; TIMES; expr { InfixOp ($1, ([], Times), $3) }

  | expr; AND; expr { InfixOp ($1, ([], And), $3) }
  | expr; OR; expr { InfixOp ($1, ([], Or), $3) }

  | expr; IMPLIES; expr { InfixOp ($1, ([], Implies), $3) }

expr:
  | general_identifier { Id $1 }
  | general_identifier; LPAREN; nonempty_list_separated_by(argument, COMMA); RPAREN { FunctionCall($1, $3) }
  
  | general_prefix_op; expr { PrefixOp ($1, $2) }
  | infix_op_helper { $1 }
  // | expr; general_postfix_op { PostfixOp ($1, $2) }

  | LPAREN; expr; RPAREN { Parenthesized $2 }

  // | quantifier; nonempty_list_separated_by(quantifier_bound, COMMA); COLON; expr { QuantifierWithBound ($1, $2, $4) }
  | quantifier; nonempty_list_separated_by(ID, COMMA); COLON; expr { QuantifierWithoutBound ($1, $2, $4) }
  // | CHOOSE; id_or_tuple; option(choose_helper); COLON; expr { Choose ($2, $3, $5) }
  | LBRACE; option(nonempty_list_separated_by(expr, COMMA)); RBRACE { ExplicitSet $2 }
  // | LBRACE; id_or_tuple; IN; expr; COLON; expr; RBRACE { SetComprehension ($2, $4, $6) }
  // | LBRACE; expr; COLON; nonempty_list_separated_by(quantifier_bound, COMMA); RBRACE { SetConstructor ($2, $4) }
  
  | expr; LBRACK; nonempty_list_separated_by(expr, COMMA); RBRACK { FunctionApplication ($1, $3) }
  // | LBRACK; nonempty_list_separated_by(quantifier_bound, COMMA); MAPTO; expr; RBRACK { FunctionConstructor ($2, $4) }
  | LBRACK; expr; RARROW; expr; RBRACK { SimpleMapping ($2, $4) }
  | LBRACK; nonempty_list_separated_by(record_constructor_helper, COMMA); RBRACK { RecordConstructor $2 }
  | LBRACK; nonempty_list_separated_by(record_type_annotation_helper, COMMA); RBRACK { RecordTypeAnnotation $2 } // [x:Int, y:Bool]
  | LBRACK; expr; EXCEPT; nonempty_list_separated_by(function_update_helper_3, COMMA); RBRACK { FunctionUpdate ($2, $4) }
  
  | TUPLE_START; nonempty_list_separated_by(expr, COMMA); TUPLE_END { TupleExpr $2 }
  // | expr; cart_product_expr_helper { CartesianProductExpr ($1, (NonEmptyList.coerce $2)) }
  // | LBRACK; expr; RBRACK; UNDERSCORE; expr { BoxActionExpr ($2, $5) }
  // | TUPLE_START; expr; TUPLE_END; UNDERSCORE; expr { DiamondActionExpr ($2, $5) }
  // | fairness_expr_helper; expr; LPAREN; expr; RPAREN { FairnessExpr ($1, $2, $4) }
  | IF; expr; THEN; expr; ELSE; expr { IfThenElseExpr ($2, $4, $6) }
  // | CASE; case_helper_1; option(case_helper_2) { let arm, arms = $2 in let a1, a2 = arm in CaseExpr(a1, a2, arms, $3) }
  | LET; nonempty_list(let_in_expr_helper); LETIN; expr { LetInExpr ($2, $4) }

  | nonempty_list(conjunc_chain_helper) { ConjunctionChain $1 }
  | nonempty_list(disconjunct_chain_helper) { DisjunctionChain $1 }
  
  | NUM { NumberLiteral $1 }
  | STRING { StringLiteral $1 }
  // | AT { AtSymbol }

  | TUPLE_START; TUPLE_END { EmptyTuple } /* Not in the BNF but used in the Paxos Spec */
  | LBRACK; ID; IN; LBRACE; RBRACE; MAPTO; ID; RBRACK { EmptyRecord } /* Not in the BNF but used in the Paxos Spec: [ x \in {} |-> Vote ] */
