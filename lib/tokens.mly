/* Lexemes */

%token INCLUDE
%token IMPORT
%token OPENED
%token DATATYPE
%token MODULE
%token PREDICATE
%token FORALL
%token EXISTS
%token VAR
%token REQUIRES ENSURES DECREASES
%token ASSERT ASSUME RETURN
%token FUNCTION LEMMA METHOD GHOST
%token TYPE
%token THIS

%token SLICE
%token ASSIGN
%token IF THEN ELSE MATCH CASE
%token SET MAP IMAP SEQ INT BOOL NAT STR
%token ADD SUB MULT DIV MOD

%token AND OR
%token EQ NEQ LTE GTE IN NOTIN

%token TRUE FALSE NULL
%token <string> STRING
%token <string> ID
%token <int>    NUM

%token LBRACE LBRACECOLON RBRACE
%token LPAREN  RPAREN
%token LANGLE  RANGLE
%token LSQBRAC RSQBRAC

%token IMPLIES
%token EXPLIES
%token EQUIV
%token QUANTIFY_SEP
%token QVAR_DOM_COLL ARROW

%token COLON
%token COMMA
%token PIPE
%token SEMI

%token SGEQ
%token NOT
%token DOT
%token EOF
%token NOLEM

%%
