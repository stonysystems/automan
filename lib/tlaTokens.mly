/* === Keywords === */
%token ASSUME ASSUMPTION AXIOM CASE CHOOSE CONSTANT CONSTANTS DOMAIN
%token ELSE ENABLED EXCEPT EXTENDS IF INSTANCE LET LOCAL MODULE
%token OTHER SF_ WF_ SUBSET THEN THEOREM UNCHANGED UNION VARIABLE VARIABLES WITH

/* === Postfix Operators === */
%token PLUSCLOSURE STARCLOSURE CARDINALITY PRIME

/* === Prefix Operators === */
%token NEG NOT ALWAYS EVENTUALLY

/* === Infix Operators === */
%token PLUS TIMES DIV EXP
%token EQ NEQ LT LE GT GE
%token IN NOTIN SUBSET_P SUBSETEQ UNION_SYM INTERSECT SETMINUS
%token CONCAT
%token AND OR IMPLIES EQUIV
%token LETIN

/* === Brackets and Delimiters === */
%token LPAREN     /* ( */
%token RPAREN     /* ) */
%token LBRACK     /* [ */
%token RBRACK     /* ] */
%token LBRACE     /* { */
%token RBRACE     /* } */
%token COMMA      /* , */ 
%token SEMI       /* ; */
%token COLON      /* : */
%token COLONCOLON /* :: */
%token COLONEQ    /* := */
%token DOT        /* . */
%token DOTDOT     /* .. */
%token ELLIPSIS   /* ... */

/* === Symbolic Operators and Arrows === */
%token PIPE       /* | */
%token BAR        /* alternative name for PIPE, if needed */
%token BAR_DASH   /* |- */
%token BAR_EQ     /* |= */
%token DARROW     /* => */
%token LARROW     /* <- */
%token RARROW     /* -> */
%token MAPTO     /* |-> */
%token DOUBLEEQ   /* == */
%token ASSIGN     /* = (redundant with EQ) */
%token TILDE_GT   /* ~> */

%token UNDERSCORE  (* _ *)
%token AT          (* @ *)

%token TUPLE_START   /* << */
%token TUPLE_END     /* >> */

%token EXCLAMATION   /* ! */

%token FORALL         /* \A */
%token EXISTS         /* \E */
%token ACTION_FORALL  /* \AA */
%token ACTION_EXISTS  /* \EE */

%token CROSS          /* \X or \times */

%token MINUS4PLUS
%token EQ4PLUS

/* === Literals and End-of-File === */
%token <string> ID
%token <string> STRING
%token <int>    NUM
%token EOF

%%
