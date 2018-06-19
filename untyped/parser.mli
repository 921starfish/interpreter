type token =
  | INT of (int)
  | BOOL of (bool)
  | ID of (string)
  | EQ
  | LT
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | MOD
  | LPAR
  | RPAR
  | LBRACKET
  | RBRACKET
  | COMMA
  | SEMICOLON
  | IF
  | THEN
  | ELSE
  | LET
  | IN
  | REC
  | AND
  | MATCH
  | WITH
  | BAR
  | END
  | UNDER
  | DSEMICOLON
  | DCOLON
  | FUN
  | RARROW
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.command
