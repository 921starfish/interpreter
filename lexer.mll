{
  open Parser
}

let digit = ['0'-'9']
let space = ' ' | '\t' | '\r' | '\n' | "　"
let alpha = ['a'-'z' 'A'-'Z' '_' ] 
let ident = alpha (alpha | digit)* 

rule token = parse
| space+      { token lexbuf }
| ";;"        { DSEMICOLON }
| "::"        { DCOLON }
| "let"       { LET }
| "rec"       { REC }
| "and"       { AND }
| "in"        { IN  }
| "="         { EQ }
| "<"         { LT }
| '+'         { PLUS }
| '-'         { MINUS }
| '*'         { TIMES }
| '/'         { DIV }
| "mod"       { MOD }
| '('         { LPAR }
| ')'         { RPAR }
| '['         { LBRACKET }
| ']'         { RBRACKET }
| ','         { COMMA }
| ';'         { SEMICOLON }
| '_'         { UNDER }
| "if"        { IF }
| "then"      { THEN }
| "else"      { ELSE }
| "true"|"false" as n { BOOL (bool_of_string n) }
| "fun"       { FUN }
| "->"        { RARROW }
| "match"     { MATCH }
| "with"      { WITH }
| '|'         { BAR }
| "end"       { END }
| digit+ as n { INT (int_of_string n) }
| "~-"(digit)+ as n { INT (int_of_string (String.sub n 1 (String.length n-1))) }
| ident  as n { ID n }
| eof         { EOF  }
| _           { failwith ("Unknown Token: " ^ Lexing.lexeme lexbuf)}
