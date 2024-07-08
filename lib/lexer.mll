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

  | "include"       { Parser.INCLUDE                        }
  | "module"        { Parser.MODULE                         }
  | "import"        { Parser.IMPORT                         }
  | "opened"        { Parser.OPENED                         }
  | "datatype"      { Parser.DATATYPE                       }
  | "predicate"     { Parser.PREDICATE                      }
  | "this"          { Parser.THIS                           }
  | "set"           { Parser.SET                            }
  | "seq"           { Parser.SEQ                            }
  | "map"           { Parser.MAP                            }
  | "int"           { Parser.INT                            }
  | "bool"          { Parser.BOOL                           }
  | "nat"           { Parser.NAT                            }
  | "string"        { Parser.STR                            }
  | "forall"        { Parser.FORALL                         }
  | "exists"        { Parser.EXISTS                         }
  | "if"            { Parser.IF                             }
  | "else"          { Parser.ELSE                           }
  | "then"          { Parser.THEN                           }
  | "match"         { Parser.MATCH                          }
  | "case"          { Parser.CASE                           }
  | "var"           { Parser.VAR                            }
  | "requires"      { Parser.REQUIRES                       }
  | "ensures"       { Parser.ENSURES                        }
  | "decreases"     { Parser.DECREASES                      }
  | "assert"        { Parser.ASSERT                         }
  | "function"      { Parser.FUNCTION                       }
  | "lemma"         { Parser.LEMMA                          }

  | "type"          { Parser.TYPE                           }
  | "true"          { Parser.TRUE                           }
  | "false"         { Parser.FALSE                          }
  | "null"          { Parser.NULL                           }

  | "."             { Parser.DOT                            }
  | "!"             { Parser.NOT                            }
  | "="             { Parser.SGEQ                           }

  | ":="            { Parser.ASSIGN                         }
  | ".."            { Parser.SLICE                          }

  | "==>"           { Parser.IMPLIES                        }
  | "<=="           { Parser.EXPLIES                        }
  | "<==>"          { Parser.EQUIV                          }
  | "<-"            { Parser.QVAR_DOM_COLL                  }
  | "=>"            { Parser.ARROW                          }
  | "::"            { Parser.QUANTIFY_SEP                   }

  | "+"             { Parser.ADD                            }
  | "-"             { Parser.SUB                            }
  | "*"             { Parser.MULT                           }
  | "/"             { Parser.DIV                            }
  | "%"             { Parser.MOD                            }

  | "=="            { Parser.EQ                             }
  | "!="            { Parser.NEQ                            }
  | "<="            { Parser.LTE                            }
  | ">="            { Parser.GTE                            }
  | "in"            { Parser.IN                             }
  | "!in"           { Parser.NOTIN                          }

  | "&&"            { Parser.AND                            }
  | "||"            { Parser.OR                             }

  | ','             { Parser.COMMA                          }
  | '{'             { Parser.LBRACE                         }
  | "{:"            { Parser.LBRACECOLON                    }
  | '}'             { Parser.RBRACE                         }
  | '('             { Parser.LPAREN                         }
  | ')'             { Parser.RPAREN                         }
  | "["             { Parser.LSQBRAC                        }
  | "]"             { Parser.RSQBRAC                        }
  | "<"             { Parser.LANGLE                         }
  | ">"             { Parser.RANGLE                         }
  | ':'             { Parser.COLON                          }
  | ';'             { Parser.SEMI                           }
  | '|'             { Parser.PIPE                           }

  | id as x         { Parser.ID(x)                          }
  | num as x        { Parser.NUM(int_of_string x)           }
  | '"'             { read_string (Buffer.create 17) lexbuf }

  | _               { raise (SyntaxError 
                        ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof             { Parser.EOF                            }


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
