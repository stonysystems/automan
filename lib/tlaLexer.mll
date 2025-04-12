{
  open Core
  exception SyntaxError of string
}

(* https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/Syntax/TLAPlusGrammar.tla *)

let white = [' ' '\t' '\r']
let id    = ['a'-'z' 'A'-'Z' '_' '\'' '`'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'' '`' '?']*
let num   = ['0'-'9']+

rule lexeme = parse
  |  white       { lexeme lexbuf }
  | '\n'         { Lexing.new_line lexbuf; lexeme lexbuf }

  | "(*"            { comments 0 lexbuf }
  | "\\*"            { single_comment lexbuf }

  | '-' '-' '-' '-' '-' * { TlaTokens.MINUS4PLUS }
  | '=' '=' '=' '=' '=' * { TlaTokens.EQ4PLUS }

  | "ASSUME"     { TlaTokens.ASSUME }
  | "ELSE"       { TlaTokens.ELSE }
  | "LOCAL"      { TlaTokens.LOCAL }
  | "UNION"      { TlaTokens.UNION }
  | "ASSUMPTION" { TlaTokens.ASSUMPTION }
  | "ENABLED"    { TlaTokens.ENABLED }
  | "MODULE"     { TlaTokens.MODULE }
  | "VARIABLE"   { TlaTokens.VARIABLE }
  | "AXIOM"      { TlaTokens.AXIOM }
  | "EXCEPT"     { TlaTokens.EXCEPT }
  | "OTHER"      { TlaTokens.OTHER }
  | "VARIABLES"  { TlaTokens.VARIABLES }
  | "CASE"       { TlaTokens.CASE }
  | "EXTENDS"    { TlaTokens.EXTENDS }
  | "SF_"        { TlaTokens.SF_ }
  | "WF_"        { TlaTokens.WF_ }
  | "CHOOSE"     { TlaTokens.CHOOSE }
  | "IF"         { TlaTokens.IF }
  | "SUBSET"     { TlaTokens.SUBSET }
  | "WITH"       { TlaTokens.WITH }
  | "CONSTANT"   { TlaTokens.CONSTANT }
  | "IN"         { TlaTokens.LETIN }
  | "THEN"       { TlaTokens.THEN }
  | "CONSTANTS"  { TlaTokens.CONSTANTS }
  | "INSTANCE"   { TlaTokens.INSTANCE }
  | "THEOREM"    { TlaTokens.THEOREM }
  | "DOMAIN"     { TlaTokens.DOMAIN }
  | "LET"        { TlaTokens.LET }
  | "UNCHANGED"  { TlaTokens.UNCHANGED }

    (* === Postfix operators === *)
  | "^+"            { TlaTokens.PLUSCLOSURE }
  | "^*"            { TlaTokens.STARCLOSURE }
  | "^#"            { TlaTokens.CARDINALITY }
  | "'"             { TlaTokens.PRIME }

  (* === Prefix operators === *)
  | "~" | "\\lnot" | "\\neg" | "\\not" { TlaTokens.NOT }
  | "-"             { TlaTokens.NEG }   (* also used as infix, distinguish in parser *)
  | "[]"            { TlaTokens.ALWAYS }
  | "<>"            { TlaTokens.EVENTUALLY }

  (* === Infix: Arithmetic === *)
  | "+"             { TlaTokens.PLUS }
  | "*"             { TlaTokens.TIMES }
  | "/" | "\\div"   { TlaTokens.DIV }
  | "^"             { TlaTokens.EXP }
  | "**"            { TlaTokens.EXP }

  (* === Infix: Comparison === *)
  | "="             { TlaTokens.EQ }
  | "/=" | "#"           { TlaTokens.NEQ }
  | "<=" | "=<" | "\\leq"  { TlaTokens.LE }
  | "<"             { TlaTokens.LT }
  | ">=" | "\\geq"  { TlaTokens.GE }
  | ">"             { TlaTokens.GT }

  (* === Infix: Set === *)
  | "\\notin"       { TlaTokens.NOTIN }
  | "\\in"          { TlaTokens.IN }
  | "\\subset"      { TlaTokens.SUBSET_P }
  | "\\subseteq"    { TlaTokens.SUBSETEQ }
  | "\\cup" | "\\union" { TlaTokens.UNION_SYM }
  | "\\cap" | "\\intersect" { TlaTokens.INTERSECT }
  | "\\"            { TlaTokens.SETMINUS }

  (* === Infix: Seq/Function === *)
  | "^^" | "@" | "\\o" { TlaTokens.CONCAT }
  | "|->" | ":>"       { TlaTokens.MAPTO }

  (* === Infix: Logic === *)
  | "/\\" | "\\land"   { TlaTokens.AND }
  | "\\/" | "\\lor"    { TlaTokens.OR }
  | "=>"               { TlaTokens.IMPLIES }
  | "<=>" | "\\equiv"  { TlaTokens.EQUIV }

  (* === Brackets and Delimiters === *)
  | "("     { TlaTokens.LPAREN }
  | ")"     { TlaTokens.RPAREN }
  | "["     { TlaTokens.LBRACK }
  | "]"     { TlaTokens.RBRACK }
  | "{"     { TlaTokens.LBRACE }
  | "}"     { TlaTokens.RBRACE }
  | ","     { TlaTokens.COMMA }
  | ";"     { TlaTokens.SEMI }
  | ":"     { TlaTokens.COLON }
  | "::"    { TlaTokens.COLONCOLON }
  | ":="    { TlaTokens.COLONEQ }
  | "..."   { TlaTokens.ELLIPSIS }
  | ".."    { TlaTokens.DOTDOT }
  | "."     { TlaTokens.DOT }

  (* === Symbolic Operators and Arrows === *)
  | "|->" | ":>"       { TlaTokens.MAPTO }
  | "=>"    { TlaTokens.DARROW }
  | "<-"    { TlaTokens.LARROW }
  | "->"    { TlaTokens.RARROW }
  | "|="    { TlaTokens.BAR_EQ }
  | "|-"    { TlaTokens.BAR_DASH }
  | "=="    { TlaTokens.DOUBLEEQ }
  (* | "="     { TlaTokens.ASSIGN } *)
  | "~>"    { TlaTokens.TILDE_GT }
  | "|"     { TlaTokens.PIPE }
  | "@"     { TlaTokens.AT }
  | "_"     { TlaTokens.UNDERSCORE }

  | "!"  { TlaTokens.EXCLAMATION }

  | "<<"  { TlaTokens.TUPLE_START }
  | ">>"  { TlaTokens.TUPLE_END }

  | "\\AA"  { TlaTokens.ACTION_FORALL }
  | "\\EE"  { TlaTokens.ACTION_EXISTS }
  | "\\A"   { TlaTokens.FORALL }
  | "\\E"   { TlaTokens.EXISTS }

  | "\\X"       { TlaTokens.CROSS }
  | "\\times"   { TlaTokens.CROSS }

  | id as x         { TlaTokens.ID(x)                          }
  | num as x        { TlaTokens.NUM(int_of_string x)           }
  | '"'             { read_string (Buffer.create 17) lexbuf }

  | _               { raise (SyntaxError 
                        ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof             { TlaTokens.EOF                            }

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
  | "*)"  { if level = 0 then lexeme lexbuf else comments (level - 1) lexbuf  }
  | "(*"  { comments (level + 1) lexbuf                                       }
  | _     { comments level lexbuf                                             }
  | eof   { raise (SyntaxError ("Undetermined comments"))                     }

and single_comment = parse
  | "\n"    { lexeme lexbuf           }
  | "\\\n"  { single_comment lexbuf   }
  | _       { single_comment lexbuf   }
