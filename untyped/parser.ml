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

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
  open Syntax
  (* ここに書いたものは，ExampleParser.mliに入らないので注意 *)
# 42 "parser.ml"
let yytransl_const = [|
  260 (* EQ *);
  261 (* LT *);
  262 (* PLUS *);
  263 (* MINUS *);
  264 (* TIMES *);
  265 (* DIV *);
  266 (* MOD *);
  267 (* LPAR *);
  268 (* RPAR *);
  269 (* LBRACKET *);
  270 (* RBRACKET *);
  271 (* COMMA *);
  272 (* SEMICOLON *);
  273 (* IF *);
  274 (* THEN *);
  275 (* ELSE *);
  276 (* LET *);
  277 (* IN *);
  278 (* REC *);
  279 (* AND *);
  280 (* MATCH *);
  281 (* WITH *);
  282 (* BAR *);
  283 (* END *);
  284 (* UNDER *);
  285 (* DSEMICOLON *);
  286 (* DCOLON *);
  287 (* FUN *);
  288 (* RARROW *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* BOOL *);
  259 (* ID *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\002\000\002\000\007\000\
\007\000\007\000\005\000\005\000\008\000\008\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\009\000\
\009\000\004\000\004\000\011\000\011\000\011\000\012\000\012\000\
\013\000\013\000\013\000\014\000\014\000\014\000\014\000\014\000\
\010\000\010\000\010\000\015\000\015\000\016\000\016\000\016\000\
\017\000\017\000\017\000\017\000\018\000\018\000\019\000\019\000\
\019\000\020\000\020\000\021\000\021\000\021\000\022\000\022\000\
\022\000\022\000\006\000\000\000"

let yylen = "\002\000\
\001\000\002\000\005\000\004\000\008\000\007\000\001\000\000\000\
\006\000\005\000\003\000\002\000\003\000\002\000\004\000\003\000\
\009\000\008\000\006\000\005\000\006\000\005\000\001\000\003\000\
\005\000\003\000\001\000\003\000\003\000\001\000\003\000\003\000\
\000\000\003\000\001\000\001\000\001\000\003\000\001\000\001\000\
\003\000\003\000\001\000\003\000\001\000\003\000\003\000\001\000\
\003\000\003\000\003\000\001\000\002\000\001\000\003\000\003\000\
\001\000\003\000\003\000\000\000\003\000\001\000\001\000\001\000\
\003\000\001\000\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\063\000\064\000\067\000\000\000\000\000\000\000\
\000\000\000\000\000\000\007\000\068\000\001\000\000\000\066\000\
\000\000\043\000\000\000\000\000\000\000\054\000\057\000\000\000\
\000\000\000\000\000\000\000\000\000\000\036\000\037\000\000\000\
\000\000\000\000\040\000\000\000\039\000\000\000\030\000\000\000\
\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\053\000\000\000\000\000\065\000\000\000\055\000\
\000\000\056\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\016\000\
\041\000\042\000\000\000\000\000\044\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\059\000\061\000\000\000\038\000\
\000\000\028\000\000\000\029\000\000\000\000\000\000\000\012\000\
\000\000\004\000\026\000\000\000\000\000\015\000\000\000\014\000\
\000\000\000\000\000\000\000\000\032\000\034\000\000\000\000\000\
\000\000\003\000\011\000\020\000\000\000\022\000\013\000\000\000\
\000\000\021\000\000\000\000\000\000\000\019\000\000\000\000\000\
\000\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\
\005\000\000\000\018\000\025\000\017\000\000\000\000\000\000\000\
\010\000\009\000"

let yydgoto = "\002\000\
\013\000\014\000\027\000\066\000\067\000\016\000\125\000\072\000\
\101\000\017\000\038\000\061\000\063\000\039\000\018\000\019\000\
\020\000\021\000\022\000\026\000\028\000\023\000"

let yysindex = "\005\000\
\001\000\000\000\000\000\000\000\000\000\152\255\152\255\152\255\
\178\255\152\255\032\000\000\000\000\000\000\000\235\254\000\000\
\110\255\000\000\009\255\099\255\127\255\000\000\000\000\183\255\
\063\255\006\255\008\255\038\255\050\255\000\000\000\000\032\000\
\032\000\053\255\000\000\206\255\000\000\052\255\000\000\055\255\
\001\255\000\000\127\255\127\255\127\255\127\255\127\255\127\255\
\127\255\127\255\000\000\053\255\211\255\000\000\152\255\000\000\
\152\255\000\000\152\255\075\255\076\255\087\255\078\255\032\000\
\152\255\224\255\255\254\032\000\032\000\152\255\035\255\000\000\
\000\000\000\000\099\255\099\255\000\000\127\255\127\255\127\255\
\032\000\152\255\083\255\096\255\000\000\000\000\098\255\000\000\
\032\000\000\000\032\000\000\000\229\255\024\255\152\255\000\000\
\152\255\000\000\000\000\086\255\100\255\000\000\152\255\000\000\
\243\255\104\255\152\255\111\255\000\000\000\000\152\255\114\255\
\152\255\000\000\000\000\000\000\152\255\000\000\000\000\152\255\
\114\255\000\000\114\255\053\255\026\255\000\000\108\255\114\255\
\122\255\030\255\032\000\152\255\000\000\032\000\123\255\152\255\
\000\000\025\000\000\000\000\000\000\000\152\255\114\255\114\255\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\131\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\006\001\000\000\246\000\165\000\057\000\000\000\000\000\000\000\
\000\000\000\000\137\255\000\000\000\000\000\000\000\000\000\000\
\138\255\000\000\000\000\000\000\000\000\146\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\131\255\000\000\000\000\000\000\000\000\142\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\192\000\219\000\000\000\084\000\111\000\138\000\
\000\000\000\000\000\000\154\255\000\000\000\000\000\000\000\000\
\000\000\000\000\138\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\155\255\000\000\000\000\000\000\036\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\143\255\000\000\036\255\000\000\000\000\000\000\141\255\143\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\036\255\036\255\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\255\255\002\000\213\255\008\000\233\255\099\000\
\037\000\000\000\000\000\086\000\082\000\000\000\234\255\000\000\
\241\255\074\000\006\000\122\000\125\000\000\000"

let yytablesize = 547
let yytable = "\015\000\
\012\000\030\000\031\000\005\000\025\000\001\000\029\000\042\000\
\040\000\083\000\036\000\032\000\041\000\033\000\045\000\046\000\
\037\000\056\000\037\000\097\000\073\000\074\000\096\000\057\000\
\077\000\053\000\051\000\098\000\035\000\075\000\076\000\037\000\
\070\000\060\000\062\000\030\000\031\000\005\000\047\000\037\000\
\037\000\064\000\071\000\037\000\113\000\032\000\132\000\033\000\
\037\000\112\000\136\000\058\000\114\000\084\000\133\000\005\000\
\008\000\087\000\137\000\081\000\037\000\121\000\035\000\094\000\
\008\000\093\000\103\000\059\000\102\000\099\000\100\000\037\000\
\071\000\037\000\054\000\037\000\037\000\055\000\037\000\069\000\
\106\000\068\000\105\000\051\000\051\000\051\000\088\000\090\000\
\037\000\089\000\108\000\092\000\062\000\115\000\143\000\116\000\
\037\000\129\000\037\000\130\000\037\000\119\000\091\000\097\000\
\135\000\122\000\048\000\049\000\050\000\123\000\055\000\126\000\
\037\000\043\000\044\000\127\000\107\000\117\000\128\000\145\000\
\146\000\078\000\079\000\080\000\113\000\089\000\118\000\003\000\
\004\000\005\000\139\000\131\000\138\000\134\000\141\000\100\000\
\124\000\006\000\037\000\007\000\144\000\037\000\132\000\136\000\
\060\000\037\000\027\000\027\000\027\000\027\000\062\000\033\000\
\003\000\004\000\005\000\035\000\027\000\027\000\027\000\027\000\
\027\000\027\000\006\000\008\000\007\000\058\000\031\000\024\000\
\008\000\104\000\140\000\024\000\110\000\027\000\109\000\010\000\
\085\000\027\000\030\000\031\000\005\000\086\000\011\000\030\000\
\031\000\005\000\000\000\000\000\032\000\000\000\033\000\000\000\
\000\000\032\000\000\000\033\000\000\000\000\000\000\000\034\000\
\000\000\000\000\000\000\000\000\052\000\035\000\030\000\031\000\
\005\000\065\000\035\000\030\000\031\000\005\000\082\000\000\000\
\032\000\000\000\033\000\000\000\000\000\032\000\000\000\033\000\
\030\000\031\000\005\000\095\000\000\000\030\000\031\000\005\000\
\111\000\035\000\032\000\000\000\033\000\000\000\035\000\032\000\
\000\000\033\000\000\000\030\000\031\000\005\000\120\000\000\000\
\000\000\000\000\000\000\035\000\000\000\032\000\000\000\033\000\
\035\000\003\000\004\000\005\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\006\000\000\000\007\000\035\000\000\000\
\000\000\008\000\000\000\000\000\009\000\000\000\000\000\000\000\
\010\000\030\000\031\000\005\000\142\000\000\000\000\000\011\000\
\030\000\031\000\005\000\032\000\000\000\033\000\000\000\000\000\
\000\000\000\000\032\000\000\000\033\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\
\000\000\000\000\000\000\035\000\052\000\052\000\052\000\052\000\
\052\000\052\000\052\000\000\000\052\000\000\000\052\000\052\000\
\052\000\000\000\052\000\052\000\000\000\052\000\000\000\052\000\
\000\000\052\000\052\000\052\000\000\000\052\000\052\000\049\000\
\049\000\049\000\049\000\049\000\049\000\049\000\000\000\049\000\
\000\000\049\000\049\000\049\000\000\000\049\000\049\000\000\000\
\049\000\000\000\049\000\000\000\049\000\049\000\049\000\000\000\
\049\000\049\000\050\000\050\000\050\000\050\000\050\000\050\000\
\050\000\000\000\050\000\000\000\050\000\050\000\050\000\000\000\
\050\000\050\000\000\000\050\000\000\000\050\000\000\000\050\000\
\050\000\050\000\000\000\050\000\050\000\051\000\051\000\051\000\
\051\000\051\000\051\000\051\000\000\000\051\000\000\000\051\000\
\051\000\051\000\000\000\051\000\051\000\000\000\051\000\000\000\
\051\000\000\000\051\000\051\000\051\000\000\000\051\000\051\000\
\048\000\048\000\048\000\048\000\000\000\000\000\000\000\000\000\
\048\000\000\000\048\000\048\000\048\000\000\000\048\000\048\000\
\000\000\048\000\000\000\048\000\000\000\048\000\048\000\048\000\
\000\000\048\000\048\000\046\000\046\000\046\000\046\000\000\000\
\000\000\000\000\000\000\046\000\000\000\046\000\046\000\046\000\
\000\000\046\000\046\000\000\000\046\000\000\000\046\000\000\000\
\046\000\046\000\046\000\000\000\046\000\046\000\047\000\047\000\
\047\000\047\000\000\000\000\000\000\000\000\000\047\000\000\000\
\047\000\047\000\047\000\000\000\047\000\047\000\000\000\047\000\
\000\000\047\000\000\000\047\000\047\000\047\000\000\000\047\000\
\047\000\045\000\045\000\000\000\000\000\000\000\000\000\000\000\
\000\000\045\000\000\000\045\000\045\000\045\000\000\000\045\000\
\045\000\000\000\045\000\000\000\045\000\000\000\045\000\045\000\
\045\000\023\000\045\000\023\000\023\000\023\000\000\000\023\000\
\023\000\000\000\023\000\000\000\023\000\000\000\023\000\023\000\
\023\000\000\000\023\000"

let yycheck = "\001\000\
\000\000\001\001\002\001\003\001\006\000\001\000\008\000\029\001\
\010\000\053\000\009\000\011\001\011\000\013\001\006\001\007\001\
\009\000\012\001\011\000\021\001\043\000\044\000\066\000\016\001\
\047\000\024\000\021\000\029\001\028\001\045\000\046\000\024\000\
\032\001\032\000\033\000\001\001\002\001\003\001\030\001\032\000\
\033\000\034\000\041\000\036\000\021\001\011\001\021\001\013\001\
\041\000\093\000\021\001\014\001\029\001\055\000\029\001\003\001\
\021\001\059\000\029\001\052\000\053\000\105\000\028\001\065\000\
\029\001\064\000\032\001\018\001\070\000\068\000\069\000\064\000\
\071\000\066\000\012\001\068\000\069\000\015\001\071\000\025\001\
\082\000\030\001\081\000\078\000\079\000\080\000\012\001\012\001\
\081\000\015\001\089\000\014\001\091\000\095\000\138\000\097\000\
\089\000\121\000\091\000\123\000\093\000\103\000\016\001\021\001\
\128\000\107\000\008\001\009\001\010\001\111\000\015\001\113\000\
\105\000\004\001\005\001\117\000\019\001\032\001\120\000\143\000\
\144\000\048\000\049\000\050\000\021\001\015\001\027\001\001\001\
\002\001\003\001\132\000\124\000\131\000\026\001\136\000\134\000\
\023\001\011\001\131\000\013\001\142\000\134\000\021\001\021\001\
\014\001\138\000\001\001\002\001\003\001\004\001\014\001\014\001\
\001\001\002\001\003\001\014\001\011\001\012\001\013\001\014\001\
\015\001\016\001\011\001\021\001\013\001\012\001\012\001\027\001\
\017\001\071\000\134\000\020\001\091\000\028\001\089\000\024\001\
\055\000\032\001\001\001\002\001\003\001\057\000\031\001\001\001\
\002\001\003\001\255\255\255\255\011\001\255\255\013\001\255\255\
\255\255\011\001\255\255\013\001\255\255\255\255\255\255\022\001\
\255\255\255\255\255\255\255\255\022\001\028\001\001\001\002\001\
\003\001\004\001\028\001\001\001\002\001\003\001\004\001\255\255\
\011\001\255\255\013\001\255\255\255\255\011\001\255\255\013\001\
\001\001\002\001\003\001\004\001\255\255\001\001\002\001\003\001\
\004\001\028\001\011\001\255\255\013\001\255\255\028\001\011\001\
\255\255\013\001\255\255\001\001\002\001\003\001\004\001\255\255\
\255\255\255\255\255\255\028\001\255\255\011\001\255\255\013\001\
\028\001\001\001\002\001\003\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\011\001\255\255\013\001\028\001\255\255\
\255\255\017\001\255\255\255\255\020\001\255\255\255\255\255\255\
\024\001\001\001\002\001\003\001\004\001\255\255\255\255\031\001\
\001\001\002\001\003\001\011\001\255\255\013\001\255\255\255\255\
\255\255\255\255\011\001\255\255\013\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\028\001\255\255\255\255\255\255\
\255\255\255\255\255\255\028\001\004\001\005\001\006\001\007\001\
\008\001\009\001\010\001\255\255\012\001\255\255\014\001\015\001\
\016\001\255\255\018\001\019\001\255\255\021\001\255\255\023\001\
\255\255\025\001\026\001\027\001\255\255\029\001\030\001\004\001\
\005\001\006\001\007\001\008\001\009\001\010\001\255\255\012\001\
\255\255\014\001\015\001\016\001\255\255\018\001\019\001\255\255\
\021\001\255\255\023\001\255\255\025\001\026\001\027\001\255\255\
\029\001\030\001\004\001\005\001\006\001\007\001\008\001\009\001\
\010\001\255\255\012\001\255\255\014\001\015\001\016\001\255\255\
\018\001\019\001\255\255\021\001\255\255\023\001\255\255\025\001\
\026\001\027\001\255\255\029\001\030\001\004\001\005\001\006\001\
\007\001\008\001\009\001\010\001\255\255\012\001\255\255\014\001\
\015\001\016\001\255\255\018\001\019\001\255\255\021\001\255\255\
\023\001\255\255\025\001\026\001\027\001\255\255\029\001\030\001\
\004\001\005\001\006\001\007\001\255\255\255\255\255\255\255\255\
\012\001\255\255\014\001\015\001\016\001\255\255\018\001\019\001\
\255\255\021\001\255\255\023\001\255\255\025\001\026\001\027\001\
\255\255\029\001\030\001\004\001\005\001\006\001\007\001\255\255\
\255\255\255\255\255\255\012\001\255\255\014\001\015\001\016\001\
\255\255\018\001\019\001\255\255\021\001\255\255\023\001\255\255\
\025\001\026\001\027\001\255\255\029\001\030\001\004\001\005\001\
\006\001\007\001\255\255\255\255\255\255\255\255\012\001\255\255\
\014\001\015\001\016\001\255\255\018\001\019\001\255\255\021\001\
\255\255\023\001\255\255\025\001\026\001\027\001\255\255\029\001\
\030\001\004\001\005\001\255\255\255\255\255\255\255\255\255\255\
\255\255\012\001\255\255\014\001\015\001\016\001\255\255\018\001\
\019\001\255\255\021\001\255\255\023\001\255\255\025\001\026\001\
\027\001\012\001\029\001\014\001\015\001\016\001\255\255\018\001\
\019\001\255\255\021\001\255\255\023\001\255\255\025\001\026\001\
\027\001\255\255\029\001"

let yynames_const = "\
  EQ\000\
  LT\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  MOD\000\
  LPAR\000\
  RPAR\000\
  LBRACKET\000\
  RBRACKET\000\
  COMMA\000\
  SEMICOLON\000\
  IF\000\
  THEN\000\
  ELSE\000\
  LET\000\
  IN\000\
  REC\000\
  AND\000\
  MATCH\000\
  WITH\000\
  BAR\000\
  END\000\
  UNDER\000\
  DSEMICOLON\000\
  DCOLON\000\
  FUN\000\
  RARROW\000\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  BOOL\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'command) in
    Obj.repr(
# 37 "parser.mly"
            ( _1 )
# 366 "parser.ml"
               : Syntax.command))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 41 "parser.mly"
                      ( CExp(_1) )
# 373 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 42 "parser.mly"
                                   ( CLet(_2,_4) )
# 381 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'patterns) in
    Obj.repr(
# 43 "parser.mly"
                                    (CLet(_2,_3))
# 389 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'pattern) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'ands) in
    Obj.repr(
# 44 "parser.mly"
                                                ( CRLet ((_3,_4,_6)::_7) )
# 399 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'patterns) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'ands) in
    Obj.repr(
# 45 "parser.mly"
                                                 ( CRLet((_3,_4,_5)::_6) )
# 409 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    Obj.repr(
# 46 "parser.mly"
        ( EoF )
# 415 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "parser.mly"
          ([])
# 421 "parser.ml"
               : 'ands))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'ands) in
    Obj.repr(
# 51 "parser.mly"
                                 ( (_2,_3,_5)::_6 )
# 431 "parser.ml"
               : 'ands))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'patterns) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'ands) in
    Obj.repr(
# 52 "parser.mly"
                                  ( (_2,_3,_4)::_5 )
# 441 "parser.ml"
               : 'ands))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 56 "parser.mly"
                    ( EFun (_1,_3) )
# 449 "parser.ml"
               : 'patterns))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'pattern) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'patterns) in
    Obj.repr(
# 57 "parser.mly"
                     ( EFun (_1,_2) )
# 457 "parser.ml"
               : 'patterns))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 61 "parser.mly"
                                        ( EFun (_1,_3) )
# 465 "parser.ml"
               : 'patternf))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'pattern) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'patternf) in
    Obj.repr(
# 62 "parser.mly"
                                            ( EFun (_1,_2) )
# 473 "parser.ml"
               : 'patternf))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 66 "parser.mly"
                                  ( EFun (_2,_4) )
# 481 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'patternf) in
    Obj.repr(
# 67 "parser.mly"
                                      ( EFun (_2,_3) )
# 489 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 6 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 5 : 'pattern) in
    let _6 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'ands) in
    let _9 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 68 "parser.mly"
                                             ( ERLet((_3,_4,_6)::_7,_9) )
# 500 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'pattern) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'patterns) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'ands) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 69 "parser.mly"
                                              ( ERLet((_3,_4,_5)::_6,_8) )
# 511 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 70 "parser.mly"
                                  ( ELet(_2,_4,_6) )
# 520 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'patterns) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 71 "parser.mly"
                                 (ELet(_2,_3,_5))
# 529 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 72 "parser.mly"
                                 ( EIf(_2,_4,_6) )
# 538 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'pattern_and_expr) in
    Obj.repr(
# 73 "parser.mly"
                                         ( EMatch(_2,_4) )
# 546 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'eq_lt_expr) in
    Obj.repr(
# 74 "parser.mly"
                              ( _1 )
# 553 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 78 "parser.mly"
                               ( [(_1,_3)] )
# 561 "parser.ml"
               : 'pattern_and_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'pattern_and_expr) in
    Obj.repr(
# 79 "parser.mly"
                                             ( (_1,_3)::_5 )
# 570 "parser.ml"
               : 'pattern_and_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_tupl_pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'pattern) in
    Obj.repr(
# 83 "parser.mly"
                                     ( PLCons(_1,_3) )
# 578 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'list_tupl_pattern) in
    Obj.repr(
# 84 "parser.mly"
                             ( _1 )
# 585 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'p_tuple_elements) in
    Obj.repr(
# 88 "parser.mly"
                                ( _2 )
# 592 "parser.ml"
               : 'list_tupl_pattern))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'p_list_elements) in
    Obj.repr(
# 89 "parser.mly"
                                      ( _2 )
# 599 "parser.ml"
               : 'list_tupl_pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_pattern) in
    Obj.repr(
# 90 "parser.mly"
                                   ( _1 )
# 606 "parser.ml"
               : 'list_tupl_pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'pattern) in
    Obj.repr(
# 94 "parser.mly"
                          ( PTCons(_1,PTCons(_3,PNil)) )
# 614 "parser.ml"
               : 'p_tuple_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'p_tuple_elements) in
    Obj.repr(
# 95 "parser.mly"
                                    ( PTCons(_1,_3) )
# 622 "parser.ml"
               : 'p_tuple_elements))
; (fun __caml_parser_env ->
    Obj.repr(
# 99 "parser.mly"
                         ( PNil )
# 628 "parser.ml"
               : 'p_list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'p_list_elements) in
    Obj.repr(
# 100 "parser.mly"
                                       ( PLCons(_1,_3) )
# 636 "parser.ml"
               : 'p_list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'pattern) in
    Obj.repr(
# 101 "parser.mly"
            ( PLCons(_1,PNil) )
# 643 "parser.ml"
               : 'p_list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 105 "parser.mly"
               ( PInt(_1) )
# 650 "parser.ml"
               : 'atomic_pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 106 "parser.mly"
               ( PBool(_1) )
# 657 "parser.ml"
               : 'atomic_pattern))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'pattern) in
    Obj.repr(
# 107 "parser.mly"
                      ( _2 )
# 664 "parser.ml"
               : 'atomic_pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 108 "parser.mly"
               ( PVar(_1) )
# 671 "parser.ml"
               : 'atomic_pattern))
; (fun __caml_parser_env ->
    Obj.repr(
# 109 "parser.mly"
               ( PUnder )
# 677 "parser.ml"
               : 'atomic_pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'eq_lt_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cons_expr) in
    Obj.repr(
# 113 "parser.mly"
                              ( EBin(OpEq,_1,_3) )
# 685 "parser.ml"
               : 'eq_lt_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'eq_lt_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cons_expr) in
    Obj.repr(
# 114 "parser.mly"
                              ( EBin(OpLt,_1,_3) )
# 693 "parser.ml"
               : 'eq_lt_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'cons_expr) in
    Obj.repr(
# 115 "parser.mly"
                  ( _1 )
# 700 "parser.ml"
               : 'eq_lt_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cons_expr) in
    Obj.repr(
# 119 "parser.mly"
                                ( EBin(OpCons,_1,_3) )
# 708 "parser.ml"
               : 'cons_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arith_expr) in
    Obj.repr(
# 120 "parser.mly"
                   ( _1 )
# 715 "parser.ml"
               : 'cons_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 124 "parser.mly"
                                  ( EBin(OpAdd,_1,_3) )
# 723 "parser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 125 "parser.mly"
                                   ( EBin(OpSub,_1,_3) )
# 731 "parser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 126 "parser.mly"
                                ( _1 )
# 738 "parser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'factor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'fapp_expr) in
    Obj.repr(
# 130 "parser.mly"
                                  ( EBin(OpMul,_1,_3) )
# 746 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'factor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'fapp_expr) in
    Obj.repr(
# 131 "parser.mly"
                                ( EBin(OpDiv,_1,_3) )
# 754 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'factor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'fapp_expr) in
    Obj.repr(
# 132 "parser.mly"
                                ( EBin(OpMod,_1,_3) )
# 762 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fapp_expr) in
    Obj.repr(
# 133 "parser.mly"
                              ( _1 )
# 769 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'fapp_expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'list_tuple_expr) in
    Obj.repr(
# 137 "parser.mly"
                                    ( EApp (_1,_2) )
# 777 "parser.ml"
               : 'fapp_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'list_tuple_expr) in
    Obj.repr(
# 138 "parser.mly"
                                    ( _1 )
# 784 "parser.ml"
               : 'fapp_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'tuple_elements) in
    Obj.repr(
# 142 "parser.mly"
                              ( _2 )
# 791 "parser.ml"
               : 'list_tuple_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'list_elements) in
    Obj.repr(
# 143 "parser.mly"
                                    ( _2 )
# 798 "parser.ml"
               : 'list_tuple_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_expr) in
    Obj.repr(
# 144 "parser.mly"
                                ( _1 )
# 805 "parser.ml"
               : 'list_tuple_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 148 "parser.mly"
                               ( ETCons(_1,ETCons(_3,ENil)) )
# 813 "parser.ml"
               : 'tuple_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tuple_elements) in
    Obj.repr(
# 149 "parser.mly"
                               ( ETCons(_1,_3) )
# 821 "parser.ml"
               : 'tuple_elements))
; (fun __caml_parser_env ->
    Obj.repr(
# 153 "parser.mly"
                         ( ENil )
# 827 "parser.ml"
               : 'list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_elements) in
    Obj.repr(
# 154 "parser.mly"
                                  ( ELCons(_1,_3) )
# 835 "parser.ml"
               : 'list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 155 "parser.mly"
         ( ELCons(_1,ENil) )
# 842 "parser.ml"
               : 'list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 159 "parser.mly"
                   ( EValue (VInt _1) )
# 849 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 160 "parser.mly"
                   ( EValue (VBool _1) )
# 856 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 161 "parser.mly"
                   ( _2 )
# 863 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 162 "parser.mly"
         ( EVar (_1) )
# 870 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 166 "parser.mly"
        ( _1 )
# 877 "parser.ml"
               : 'var))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Syntax.command)
