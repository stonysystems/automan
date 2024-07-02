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
%token ASSERT
%token FUNCTION
%token LEMMA
%token TYPE

%token SLICE
%token ASSIGN
%token IF ELSE THEN
%token INT BOOL NAT SEQ MAP SET OPTION
%token ADD SUB MULT DIV MOD

%token AND OR
%token EQ NEQ LTE GTE IN NOTIN

%token <string> STRING
%token <string> ID
%token <int>    NUM

%token LBRACE  RBRACE
%token LPAREN  RPAREN
%token LANGLE  RANGLE
%token LSQBRAC RSQBRAC

%token IMPLIESL
%token IMPLIESR
%token IMPLIESBOTH
%token SUCHTHAT

%token COLON
%token COMMA
%token PIPE
%token SEMI

%token SGEQ
%token NOT
%token QUESTIONM
%token ATTRIBUTE
%token EOF

%left  SUCHTHAT
%right IMPLIESL IMPLIESR IMPLIESBOTH

%left  SEMI
%left  ELSE

%left  PIPE

%left  AND OR
%left  EQ NEQ LTE GTE IN NOTIN

%left  LSQBRAC

%left  LBRACE
%left  LANGLE  
%left  RANGLE

%left  ADD  SUB
%left  MULT DIV
%left  MOD

%left  SLICE

%left  NOT
%left  QUESTIONM
%left  ATTRIBUTE

%start file
%type <Syntax.ParserPass.file_level option> file

%%


file:
  | i = incl_dcl    { Some i } 
  | m = module_def  { Some m }
  | EOF             { None   }

incl_dcl:
  | INCLUDE; p = STRING  { Syntax.ParserPass.Include p }

module_def:
  | MODULE; n = ID; LBRACE; i = module_items;  RBRACE { Syntax.ParserPass.Module (n, i) }

module_items:
  |                                         { []            }
  | item = module_item; rest = module_items { item :: rest  }

module_item:
  | i = import_dcl   { i }
  | d = datatype_df  { d }
  | t = alias_df     { t }
  | p = predicate_df { p }
  | f = function_df  { f }
  | l = lemma_df     { l }

import_dcl:
  | IMPORT; OPENED; p = ID { Syntax.ParserPass.Import p }

datatype_df:
  | DATATYPE; a = ID; SGEQ; c = datatype_ctors; { 
     Syntax.ParserPass.DatatypeDef (a, c) 
   }

datatype_ctors:
  | a = separated_list(PIPE, datatype_ctor) { a }

datatype_ctor:
  | a = ID; LPAREN; b = formals; RPAREN; { Syntax.ParserPass.DatatypeCtor (a, b) }

formals:
  | a = separated_list(COMMA, formal)  { a }

formal:
  | a = ID; COLON; b = tp { Syntax.ParserPass.Formal(a, b) }


/* expr start */

args:
  | a = separated_list(COMMA, expr) { a }

arith:
  | a = expr; ADD;  b = expr { Syntax.ParserPass.Add(a, b)  }
  | a = expr; SUB;  b = expr { Syntax.ParserPass.Sub(a, b)  }
  | a = expr; MULT; b = expr { Syntax.ParserPass.Mult(a, b) }
  | a = expr; DIV;  b = expr { Syntax.ParserPass.Div(a, b)  }
  | a = expr; MOD;  b = expr { Syntax.ParserPass.Mod(a, b)  }

boolean:
  | a = expr; AND; b = expr { Syntax.ParserPass.And(a, b)                }
  | a = expr; OR;  b = expr { Syntax.ParserPass.Or(a, b)                 }
  | AND; b = expr           { Syntax.ParserPass.And(Syntax.ParserPass.ExprBlank, b) }
  | OR; b = expr            { Syntax.ParserPass.Or(Syntax.ParserPass.ExprBlank, b)  }

cmp:
  | a = expr; EQ;     b = expr      { Syntax.ParserPass.Eq(a, b)     }
  | a = expr; NEQ;    b = expr      { Syntax.ParserPass.Neq(a, b)    }
  | a = expr; LANGLE; b = expr      { Syntax.ParserPass.Lt(a, b)     }
  | a = expr; LTE;    b = expr      { Syntax.ParserPass.Lte(a, b)    }
  | a = expr; RANGLE; b = expr      { Syntax.ParserPass.Gt(a, b)     }
  | a = expr; GTE;    b = expr      { Syntax.ParserPass.Gte(a, b)    }
  | a = expr; IN;     b = expr      { Syntax.ParserPass.In(a, b)     }
  | a = expr; NOTIN;  b = expr      { Syntax.ParserPass.NotIn(a, b)  }

expr_implies:
  | a = expr; IMPLIESBOTH;  b = expr    { Syntax.ParserPass.ImpliesBoth(a, b)  }
  | a = expr; IMPLIESL;     b = expr    { Syntax.ParserPass.ImpliesL(a, b)     }
  | a = expr; IMPLIESR;     b = expr    { Syntax.ParserPass.ImpliesR(a, b)     }

expr_q_var:
  | a = expr_id { a }

q_var:
  | a = separated_nonempty_list(COMMA, expr_q_var)  
                                          { Syntax.ParserPass.QVar(a)          }

expr_qtfier:
  | FORALL; a = q_var; SUCHTHAT; b = expr 
                                          { Syntax.ParserPass.QForall(a, b)    }
  | EXISTS; a = q_var; SUCHTHAT; b = expr { Syntax.ParserPass.QExists(a, b)    }

expr_bin_op:
  | a = arith                             { Syntax.ParserPass.Arith(a)         }
  | a = boolean                           { Syntax.ParserPass.Bool(a)          }
  | a = cmp                               { Syntax.ParserPass.Cmp(a)           } 
  | a = expr; ATTRIBUTE; LPAREN;
    b = i_assigns; RPAREN                 { Syntax.ParserPass.AUpdate(a, b)    }
  | a = expr; ATTRIBUTE; b = expr         
                                          { Syntax.ParserPass.Attribute(a, b)  }

expr_if:
  | IF; a = expr; THEN; b = expr; ELSE; c = expr    { Syntax.ParserPass.ExprIf(a, b, c) }

map_ctor:
  | MAP; LSQBRAC; a = separated_list(COMMA, i_assign); RSQBRAC 
                                          { Syntax.ParserPass.MapCtorSpec(a)   }
  
  | MAP; a = ID; PIPE; b = expr; SUCHTHAT; c = expr
                                          { Syntax.ParserPass.MapCtorItor(ExprId(a), b, c) }

seq_ctor:
  | LSQBRAC; a = separated_list(COMMA, expr); RSQBRAC
                                          { Syntax.ParserPass.SeqCtorSpec(a)   }

set_ctor:
  | LBRACE; a = separated_list(COMMA, expr); RBRACE
                                          { Syntax.ParserPass.SetCtorSpec(a)             }
  // | SET; a = ID; PIPE; b = expr           { Syntax.ParserPass.SetCtorItor(ExprId(a), b)  }
  // | SET; a = expr; PIPE; b = expr           { Syntax.ParserPass.SetCtorItor(a, b)  }
  | SET; a = separated_list(COMMA, ID); PIPE; b = expr; SUCHTHAT; c = expr
                                          { Syntax.ParserPass.SetCtorItorSuchThat(a, b, c) }

expr_coll_ctor:
  | a = map_ctor                          { Syntax.ParserPass.MapCtor(a)       }
  | a = seq_ctor                          { Syntax.ParserPass.SeqCtor(a)       }
  | a = set_ctor                          { Syntax.ParserPass.SetCtor(a)       }

hoare:
  | REQUIRES; a = expr;                   { Syntax.ParserPass.Requires(a)      }
  | ENSURES;  a = expr;                   { Syntax.ParserPass.Ensures(a)       }

decrases:
  | DECREASES; a = expr                   { Syntax.ParserPass.Decreases(a)     }

ctst:
  | a = hoare                             { a                       }
  | a = decrases                          { a                       }

ctsts:
  |                                       { []                      }
  | a = ctst; b = ctsts                   { a :: b                  }

i_assign:
  | a = expr; ASSIGN; b = expr            { Syntax.ParserPass.IAssign(a, b)    }

i_assigns:
  | a = i_assign                          { [a]                     }
  | a = i_assign; COMMA; b = i_assigns
                                          { a :: b                  }


/* Note that the order of the following expr determine its priviledge */

expr_call:
  | a = ID; LPAREN; b = args; RPAREN      { Syntax.ParserPass.ExprCall(a, b)   }

expr_num:
  | a = NUM                               { Syntax.ParserPass.ExprNum(a)       }

expr_scpt:
  | a = expr; LSQBRAC; b = expr; RSQBRAC  { Syntax.ParserPass.ExprScpt(a, b)   }

expr_len:
  | PIPE; a = expr; PIPE                  { Syntax.ParserPass.ExprLen(a)       }

expr_question_m:
  | a = expr; QUESTIONM                   { Syntax.ParserPass.ExprQuestionM(a) }

expr_not:
  | NOT; a = expr                         { Syntax.ParserPass.ExprNot(a)       }

expr_let_bind:
  | a = stmt_vassign; SEMI; b = expr  
                                          { Syntax.ParserPass.ExprLetBind(a, b)} 

expr_coll_a_update:
  | a = expr; LSQBRAC; b = i_assigns; RSQBRAC
                                          { Syntax.ParserPass.ExprCollAUpdate(a, b) }

expr_id:
  | a = ID                                { Syntax.ParserPass.ExprId(a)        }

expr_tuple:
  | a = expr; COMMA; b = expr             { [a; b]                  }
  | a = expr; COMMA; b = expr_tuple       { a :: b                  }

expr_slice:
  | a = expr; SLICE; b = expr             { Syntax.ParserPass.SliceLR(a, b)    }
  | SLICE; a = expr                       { Syntax.ParserPass.SliceNoL(a)      }
  | a = expr; SLICE                       { Syntax.ParserPass.SliceNoR(a)      }

expr:
  | LPAREN; a = expr; RPAREN              { Syntax.ParserPass.PExpr(a)         }
  | a = expr_call                         { a                       }
  | a = expr_num                          { a                       }
  | a = expr_bin_op                       { Syntax.ParserPass.ExprBinOp(a)     }
  | a = expr_scpt                         { a                       }
  | a = expr_if                           { a                       }
  | a = expr_len                          { a                       }
  | a = expr_coll_ctor                    { Syntax.ParserPass.ExprCollCtor(a)  }
  | a = expr_question_m                   { a                       }
  | a = expr_let_bind                     { a                       } 
  | a = expr_coll_a_update                { a                       }
  | a = expr_id                           { a                       }
  | a = expr_qtfier                       { Syntax.ParserPass.ExprQtfier(a)    }
  | LPAREN; a = expr_tuple; RPAREN        { Syntax.ParserPass.ExprTuple(a)     }
  | a = expr_not                          { a                       }
  | a = expr_slice                        { Syntax.ParserPass.ExprSlice(a)     }
  | a = expr_implies                      { Syntax.ParserPass.ExprImplies(a)   }

/* expr end   */

/* stmt start */

stmts_braced:
  | LBRACE; a = stmts; RBRACE             { Syntax.ParserPass.StmtsBraced(a)   }

stmt_if:
  | IF; a = expr; b = stmts_braced        { Syntax.ParserPass.StmtIf(a, b)     }

stmt_if_else:
  | a = stmt_if; ELSE; b = stmts_braced
                                          { Syntax.ParserPass.StmtIfElse(a, b) }

stmt_if_elif:
  | a = stmt_if                           { a                       }
  | a = stmt_if_else                      { a                       }
  | a = stmt_if; ELSE; b = stmt_if_elif   { Syntax.ParserPass.StmtIfElif(a, b) }

assigned_ids:
  | a = ID; COMMA; b = ID                 { [a; b]                  }
  | a = ID; COMMA; b = assigned_ids       { a :: b                  }

assigned:
  | LPAREN; a = assigned_ids; RPAREN      { Syntax.ParserPass.AssignedTpl(a)   }
  | a = ID                                { Syntax.ParserPass.AssignedId(a)    }

stmt_assign:
  | a = assigned; ASSIGN; b = expr            
                                          { Syntax.ParserPass.StmtAssign(a, b) }
stmt_vassign:
  | VAR; a = assigned; ASSIGN; b = expr   { Syntax.ParserPass.StmtVAssign(a, b)}

stmt_sp_by_semi:
  | a = stmt_assign                       { a                       }
  | a = stmt_vassign                      { a                       }
  | ASSERT; a = expr                      { Syntax.ParserPass.StmtAssert(a)    }
  | a = ID; LPAREN; b = args; RPAREN      { Syntax.ParserPass.StmtCall(a, b)   }

stmt:
  | a = stmt_sp_by_semi; SEMI             { a                       }
  | a = stmts_braced                      { a                       }
  | a = stmt_if_elif                      { a                       }

stmts:
  |                                       { []                      }
  | item = stmt; rest = stmts             { item :: rest            }

/* stmt end */

predicate_df:
  | PREDICATE; a = ID; 
    LPAREN; b = formals; RPAREN; 
    c = ctsts; 
    LBRACE; d = expr; RBRACE              { Syntax.ParserPass.Predicate ((), a, b, c, d) }

lemma_df:
  | LEMMA; a = ID;
    LPAREN; b = formals; RPAREN;
    c = ctsts;
    LBRACE; d = stmts; RBRACE;                         
                                          { Syntax.ParserPass.Lemma (a, b, c, d)     } 

return_func:
  | a = tp                                { Syntax.ParserPass.ReturnFuncSgl a        }
  | LPAREN; a = separated_list(COMMA, tp); RPAREN
                                          { Syntax.ParserPass.ReturnFuncTpl a        }   

function_df:
  | FUNCTION; a = ID; 
    LPAREN; b = formals; RPAREN;
    COLON; c = return_func;
    d = ctsts
    LBRACE; e = expr; RBRACE              { Syntax.ParserPass.Function (a, b, c, d, e)}

alias_df:
  | TYPE; a = ID; SGEQ; b = tp            { Syntax.ParserPass.Alias (a, b)            }

tp:
  | a = tp_coll     { Syntax.ParserPass.TpColl a }
  | a = tp_prmt     { Syntax.ParserPass.TpPrmt a }
  | a = ID          { Syntax.ParserPass.TpId a   }
  | OPTION; LANGLE; a = tp; RANGLE              { Syntax.ParserPass.TpOption(a) }

tp_coll:
  | SEQ; LANGLE; b = tp; RANGLE                 { Syntax.ParserPass.TpCollSeq b          }
  | SET; LANGLE; b = tp; RANGLE                 { Syntax.ParserPass.TpCollSet b          }
  | MAP; LANGLE; a = tp; COMMA; b = tp; RANGLE  { Syntax.ParserPass.TpCollMap (a, b)     } 
  | a = ID; LANGLE; b = tp; COMMA; c = tp; RANGLE 
                                                { Syntax.ParserPass.TpIdCollMap(a, b, c) }

tp_prmt:
  | INT   { Syntax.ParserPass.PrmtInt    }
  | BOOL  { Syntax.ParserPass.PrmtBool   }
  | NAT   { Syntax.ParserPass.PrmtNat    }

