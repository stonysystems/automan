{
  open Core
  exception SyntaxError of string
}

let white = [' ' '\t' '\r']
let id    = ['a'-'z' 'A'-'Z' '_' '\'' '`'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'' '`' '?']*
let num   = ['0'-'9']+

rule lexeme = parse
  |  white          { lexeme lexbuf                         }
  | '\n'            { Lexing.new_line lexbuf; lexeme lexbuf }

  | "/*"            { comments 0 lexbuf                     }
  | "//"            { single_comment lexbuf                 }

  | "include"       { Tokens.INCLUDE                        }
  | "module"        { Tokens.MODULE                         }
  | "import"        { Tokens.IMPORT                         }
  | "opened"        { Tokens.OPENED                         }
  | "datatype"      { Tokens.DATATYPE                       }
  | "predicate"     { Tokens.PREDICATE                      }
  | "this"          { Tokens.THIS                           }
  | "set"           { Tokens.SET                            }
  | "seq"           { Tokens.SEQ                            }
  | "map"           { Tokens.MAP                            }
  | "int"           { Tokens.INT                            }
  | "bool"          { Tokens.BOOL                           }
  | "nat"           { Tokens.NAT                            }
  | "string"        { Tokens.STR                            }
  | "forall"        { Tokens.FORALL                         }
  | "exists"        { Tokens.EXISTS                         }
  | "if"            { Tokens.IF                             }
  | "else"          { Tokens.ELSE                           }
  | "then"          { Tokens.THEN                           }
  | "match"         { Tokens.MATCH                          }
  | "case"          { Tokens.CASE                           }
  | "var"           { Tokens.VAR                            }
  | "requires"      { Tokens.REQUIRES                       }
  | "ensures"       { Tokens.ENSURES                        }
  | "decreases"     { Tokens.DECREASES                      }
  | "assert"        { Tokens.ASSERT                         }
  | "assume"        { Tokens.ASSUME                         }
  | "return"        { Tokens.RETURN                         }
  | "function"      { Tokens.FUNCTION                       }
  | "lemma"         { Tokens.LEMMA                          }
  | "method"        { Tokens.METHOD                         }
  | "ghost"         { Tokens.GHOST                          }

  | "type"          { Tokens.TYPE                           }
  | "true"          { Tokens.TRUE                           }
  | "false"         { Tokens.FALSE                          }
  | "null"          { Tokens.NULL                           }

  | "."             { Tokens.DOT                            }
  | "!"             { Tokens.NOT                            }
  | "="             { Tokens.SGEQ                           }

  | ":="            { Tokens.ASSIGN                         }
  | ".."            { Tokens.SLICE                          }

  | "==>"           { Tokens.IMPLIES                        }
  | "<=="           { Tokens.EXPLIES                        }
  | "<==>"          { Tokens.EQUIV                          }
  | "<-"            { Tokens.QVAR_DOM_COLL                  }
  | "=>"            { Tokens.ARROW                          }
  | "::"            { Tokens.QUANTIFY_SEP                   }

  | "+"             { Tokens.ADD                            }
  | "-"             { Tokens.SUB                            }
  | "*"             { Tokens.MULT                           }
  | "/"             { Tokens.DIV                            }
  | "%"             { Tokens.MOD                            }

  | "=="            { Tokens.EQ                             }
  | "!="            { Tokens.NEQ                            }
  | "<="            { Tokens.LTE                            }
  | ">="            { Tokens.GTE                            }
  | "in"            { Tokens.IN                             }
  | "!in"           { Tokens.NOTIN                          }

  | "&&"            { Tokens.AND                            }
  | "||"            { Tokens.OR                             }

  | ','             { Tokens.COMMA                          }
  | '{'             { Tokens.LBRACE                         }
  | "{:"            { Tokens.LBRACECOLON                    }
  | '}'             { Tokens.RBRACE                         }
  | '('             { Tokens.LPAREN                         }
  | ')'             { Tokens.RPAREN                         }
  | "["             { Tokens.LSQBRAC                        }
  | "]"             { Tokens.RSQBRAC                        }
  | "<"             { Tokens.LANGLE                         }
  | ">"             { Tokens.RANGLE                         }
  | ':'             { Tokens.COLON                          }
  | ';'             { Tokens.SEMI                           }
  | '|'             { Tokens.PIPE                           }

  | id as x         { Tokens.ID(x)                          }
  | num as x        { Tokens.NUM(int_of_string x)           }
  | '"'             { read_string (Buffer.create 17) lexbuf }

  | _               { raise (SyntaxError 
                        ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof             { Tokens.EOF                            }


and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf)                          }
  | '\\' '/'  { Buffer.add_char buf '/';    read_string buf lexbuf    }
  | '\\' '\\' { Buffer.add_char buf '\\';   read_string buf lexbuf    }
  | '\\' 'b'  { Buffer.add_char buf '\b';   read_string buf lexbuf    }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf    }
  | '\\' 'n'  { Buffer.add_char buf '\n';   read_string buf lexbuf    }
  | '\\' 'r'  { Buffer.add_char buf '\r';   read_string buf lexbuf    }
  | '\\' 't'  { Buffer.add_char buf '\t';   read_string buf lexbuf    }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { 
    raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof       { raise (SyntaxError ("String is not terminated"))    }

and comments level = parse
  | "*/"  { if level = 0 then lexeme lexbuf else comments (level - 1) lexbuf  }
  | "/*"  { comments (level + 1) lexbuf                                       }
  | _     { comments level lexbuf                                             }
  | eof   { raise (SyntaxError ("Undetermined comments"))                     }

and single_comment = parse
  | "\n"    { lexeme lexbuf           }
  | "\\\n"  { single_comment lexbuf   }
  | _       { single_comment lexbuf   }
