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
\007\000\005\000\005\000\008\000\008\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\009\000\009\000\
\004\000\004\000\011\000\011\000\011\000\012\000\012\000\013\000\
\013\000\013\000\014\000\014\000\014\000\014\000\014\000\010\000\
\010\000\010\000\015\000\015\000\016\000\016\000\016\000\017\000\
\017\000\017\000\017\000\018\000\018\000\019\000\019\000\019\000\
\020\000\020\000\021\000\021\000\021\000\022\000\022\000\022\000\
\022\000\006\000\000\000"

let yylen = "\002\000\
\001\000\002\000\005\000\004\000\008\000\007\000\001\000\000\000\
\006\000\003\000\002\000\003\000\002\000\004\000\003\000\009\000\
\008\000\006\000\005\000\006\000\005\000\001\000\003\000\005\000\
\003\000\001\000\003\000\003\000\001\000\003\000\003\000\000\000\
\003\000\001\000\001\000\001\000\003\000\001\000\001\000\003\000\
\003\000\001\000\003\000\001\000\003\000\003\000\001\000\003\000\
\003\000\003\000\001\000\002\000\001\000\003\000\003\000\001\000\
\003\000\003\000\000\000\003\000\001\000\001\000\001\000\003\000\
\001\000\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\062\000\063\000\066\000\000\000\000\000\000\000\
\000\000\000\000\000\000\007\000\067\000\001\000\000\000\065\000\
\000\000\042\000\000\000\000\000\000\000\053\000\056\000\000\000\
\000\000\000\000\000\000\000\000\000\000\035\000\036\000\000\000\
\000\000\000\000\039\000\000\000\038\000\000\000\029\000\000\000\
\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\052\000\000\000\000\000\064\000\000\000\054\000\
\000\000\055\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\015\000\
\040\000\041\000\000\000\000\000\043\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\058\000\060\000\000\000\037\000\
\000\000\027\000\000\000\028\000\000\000\000\000\000\000\004\000\
\000\000\011\000\025\000\000\000\000\000\014\000\000\000\013\000\
\000\000\000\000\000\000\000\000\031\000\033\000\000\000\000\000\
\000\000\003\000\019\000\010\000\000\000\021\000\012\000\000\000\
\000\000\020\000\000\000\000\000\000\000\018\000\000\000\000\000\
\000\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\
\005\000\000\000\017\000\024\000\016\000\000\000\000\000\009\000"

let yydgoto = "\002\000\
\013\000\014\000\027\000\062\000\066\000\016\000\125\000\072\000\
\101\000\017\000\038\000\061\000\063\000\039\000\018\000\019\000\
\020\000\021\000\022\000\026\000\028\000\023\000"

let yysindex = "\003\000\
\001\000\000\000\000\000\000\000\000\000\026\255\026\255\026\255\
\123\255\026\255\008\255\000\000\000\000\000\000\242\254\000\000\
\016\255\000\000\006\255\077\255\158\255\000\000\000\000\145\255\
\040\255\013\255\022\255\045\255\052\255\000\000\000\000\151\255\
\151\255\008\255\000\000\044\255\000\000\070\255\000\000\066\255\
\021\255\000\000\158\255\158\255\158\255\158\255\158\255\158\255\
\158\255\158\255\000\000\008\255\105\255\000\000\026\255\000\000\
\026\255\000\000\026\255\083\255\093\255\095\255\109\255\008\255\
\026\255\237\254\111\255\151\255\151\255\026\255\042\255\000\000\
\000\000\000\000\077\255\077\255\000\000\158\255\158\255\158\255\
\008\255\026\255\106\255\118\255\000\000\000\000\121\255\000\000\
\151\255\000\000\151\255\000\000\114\255\241\254\026\255\000\000\
\026\255\000\000\000\000\112\255\116\255\000\000\026\255\000\000\
\126\255\128\255\026\255\135\255\000\000\000\000\026\255\132\255\
\026\255\000\000\000\000\000\000\026\255\000\000\000\000\026\255\
\132\255\000\000\132\255\008\255\059\255\000\000\131\255\132\255\
\142\255\061\255\008\255\026\255\000\000\151\255\144\255\026\255\
\000\000\162\255\000\000\000\000\000\000\026\255\132\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\154\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\222\255\000\000\164\000\083\000\176\255\000\000\000\000\000\000\
\000\000\000\000\156\255\000\000\000\000\000\000\000\000\000\000\
\160\255\000\000\000\000\000\000\000\000\019\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\154\255\000\000\000\000\000\000\000\000\161\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\110\000\137\000\000\000\203\255\029\000\056\000\
\000\000\000\000\000\000\164\255\000\000\000\000\000\000\000\000\
\000\000\000\000\160\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\165\255\000\000\000\000\000\000\063\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\157\255\000\000\063\255\000\000\000\000\000\000\166\255\157\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\063\255\000\000"

let yygindex = "\000\000\
\000\000\000\000\255\255\250\255\219\255\008\000\206\255\101\000\
\053\000\000\000\000\000\100\000\105\000\000\000\060\000\000\000\
\092\000\072\000\243\255\143\000\147\000\000\000"

let yytablesize = 449
let yytable = "\015\000\
\012\000\095\000\036\000\001\000\025\000\113\000\029\000\051\000\
\040\000\096\000\005\000\045\000\046\000\114\000\042\000\083\000\
\037\000\053\000\041\000\043\000\044\000\026\000\026\000\005\000\
\056\000\060\000\003\000\004\000\005\000\098\000\026\000\037\000\
\026\000\026\000\026\000\047\000\006\000\057\000\007\000\037\000\
\037\000\064\000\008\000\067\000\005\000\024\000\005\000\065\000\
\071\000\010\000\026\000\054\000\070\000\084\000\055\000\112\000\
\011\000\087\000\058\000\081\000\067\000\099\000\100\000\094\000\
\051\000\051\000\051\000\121\000\102\000\059\000\129\000\093\000\
\130\000\103\000\067\000\037\000\037\000\135\000\071\000\132\000\
\106\000\136\000\108\000\008\000\048\000\049\000\050\000\133\000\
\105\000\137\000\069\000\008\000\144\000\115\000\088\000\116\000\
\037\000\089\000\037\000\068\000\067\000\119\000\073\000\074\000\
\090\000\122\000\077\000\005\000\082\000\123\000\091\000\126\000\
\067\000\005\000\097\000\127\000\005\000\111\000\128\000\078\000\
\079\000\080\000\092\000\030\000\031\000\005\000\095\000\100\000\
\005\000\120\000\139\000\131\000\055\000\032\000\141\000\033\000\
\075\000\076\000\138\000\107\000\143\000\037\000\118\000\117\000\
\034\000\030\000\031\000\005\000\113\000\089\000\035\000\030\000\
\031\000\005\000\124\000\032\000\134\000\033\000\003\000\004\000\
\005\000\032\000\132\000\033\000\136\000\142\000\052\000\059\000\
\006\000\061\000\007\000\104\000\035\000\032\000\034\000\057\000\
\030\000\008\000\035\000\051\000\051\000\051\000\051\000\051\000\
\051\000\051\000\140\000\051\000\109\000\051\000\051\000\051\000\
\023\000\051\000\051\000\110\000\051\000\085\000\051\000\000\000\
\051\000\051\000\051\000\086\000\051\000\051\000\048\000\048\000\
\048\000\048\000\048\000\048\000\048\000\000\000\048\000\000\000\
\048\000\048\000\048\000\000\000\048\000\048\000\000\000\048\000\
\000\000\048\000\000\000\048\000\048\000\048\000\000\000\048\000\
\048\000\022\000\000\000\022\000\022\000\022\000\000\000\022\000\
\022\000\000\000\022\000\000\000\022\000\000\000\022\000\022\000\
\022\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\
\000\000\003\000\004\000\005\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\006\000\000\000\007\000\000\000\000\000\
\000\000\008\000\000\000\000\000\009\000\000\000\000\000\000\000\
\010\000\000\000\000\000\000\000\000\000\000\000\000\000\011\000\
\049\000\049\000\049\000\049\000\049\000\049\000\049\000\000\000\
\049\000\000\000\049\000\049\000\049\000\000\000\049\000\049\000\
\000\000\049\000\000\000\049\000\000\000\049\000\049\000\049\000\
\000\000\049\000\049\000\050\000\050\000\050\000\050\000\050\000\
\050\000\050\000\000\000\050\000\000\000\050\000\050\000\050\000\
\000\000\050\000\050\000\000\000\050\000\000\000\050\000\000\000\
\050\000\050\000\050\000\000\000\050\000\050\000\047\000\047\000\
\047\000\047\000\000\000\000\000\000\000\000\000\047\000\000\000\
\047\000\047\000\047\000\000\000\047\000\047\000\000\000\047\000\
\000\000\047\000\000\000\047\000\047\000\047\000\000\000\047\000\
\047\000\045\000\045\000\045\000\045\000\000\000\000\000\000\000\
\000\000\045\000\000\000\045\000\045\000\045\000\000\000\045\000\
\045\000\000\000\045\000\000\000\045\000\000\000\045\000\045\000\
\045\000\000\000\045\000\045\000\046\000\046\000\046\000\046\000\
\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\
\046\000\000\000\046\000\046\000\000\000\046\000\000\000\046\000\
\000\000\046\000\046\000\046\000\000\000\046\000\046\000\044\000\
\044\000\000\000\000\000\000\000\000\000\000\000\000\000\044\000\
\000\000\044\000\044\000\044\000\000\000\044\000\044\000\000\000\
\044\000\000\000\044\000\000\000\044\000\044\000\044\000\000\000\
\044\000"

let yycheck = "\001\000\
\000\000\021\001\009\000\001\000\006\000\021\001\008\000\021\000\
\010\000\029\001\003\001\006\001\007\001\029\001\029\001\053\000\
\009\000\024\000\011\000\004\001\005\001\003\001\004\001\003\001\
\012\001\032\000\001\001\002\001\003\001\067\000\012\001\024\000\
\014\001\015\001\016\001\030\001\011\001\016\001\013\001\032\000\
\033\000\034\000\017\001\036\000\003\001\020\001\003\001\004\001\
\041\000\024\001\032\001\012\001\032\001\055\000\015\001\093\000\
\031\001\059\000\014\001\052\000\053\000\068\000\069\000\065\000\
\078\000\079\000\080\000\105\000\070\000\018\001\121\000\064\000\
\123\000\032\001\067\000\068\000\069\000\128\000\071\000\021\001\
\082\000\021\001\089\000\021\001\008\001\009\001\010\001\029\001\
\081\000\029\001\025\001\029\001\143\000\095\000\012\001\097\000\
\089\000\015\001\091\000\030\001\093\000\103\000\043\000\044\000\
\012\001\107\000\047\000\003\001\004\001\111\000\016\001\113\000\
\105\000\003\001\004\001\117\000\003\001\004\001\120\000\048\000\
\049\000\050\000\014\001\001\001\002\001\003\001\021\001\134\000\
\003\001\004\001\132\000\124\000\015\001\011\001\136\000\013\001\
\045\000\046\000\131\000\019\001\142\000\134\000\027\001\032\001\
\022\001\001\001\002\001\003\001\021\001\015\001\028\001\001\001\
\002\001\003\001\023\001\011\001\026\001\013\001\001\001\002\001\
\003\001\011\001\021\001\013\001\021\001\004\001\022\001\014\001\
\011\001\014\001\013\001\071\000\028\001\014\001\014\001\012\001\
\012\001\021\001\028\001\004\001\005\001\006\001\007\001\008\001\
\009\001\010\001\134\000\012\001\089\000\014\001\015\001\016\001\
\027\001\018\001\019\001\091\000\021\001\055\000\023\001\255\255\
\025\001\026\001\027\001\057\000\029\001\030\001\004\001\005\001\
\006\001\007\001\008\001\009\001\010\001\255\255\012\001\255\255\
\014\001\015\001\016\001\255\255\018\001\019\001\255\255\021\001\
\255\255\023\001\255\255\025\001\026\001\027\001\255\255\029\001\
\030\001\012\001\255\255\014\001\015\001\016\001\255\255\018\001\
\019\001\255\255\021\001\255\255\023\001\255\255\025\001\026\001\
\027\001\255\255\029\001\255\255\255\255\255\255\255\255\255\255\
\255\255\001\001\002\001\003\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\011\001\255\255\013\001\255\255\255\255\
\255\255\017\001\255\255\255\255\020\001\255\255\255\255\255\255\
\024\001\255\255\255\255\255\255\255\255\255\255\255\255\031\001\
\004\001\005\001\006\001\007\001\008\001\009\001\010\001\255\255\
\012\001\255\255\014\001\015\001\016\001\255\255\018\001\019\001\
\255\255\021\001\255\255\023\001\255\255\025\001\026\001\027\001\
\255\255\029\001\030\001\004\001\005\001\006\001\007\001\008\001\
\009\001\010\001\255\255\012\001\255\255\014\001\015\001\016\001\
\255\255\018\001\019\001\255\255\021\001\255\255\023\001\255\255\
\025\001\026\001\027\001\255\255\029\001\030\001\004\001\005\001\
\006\001\007\001\255\255\255\255\255\255\255\255\012\001\255\255\
\014\001\015\001\016\001\255\255\018\001\019\001\255\255\021\001\
\255\255\023\001\255\255\025\001\026\001\027\001\255\255\029\001\
\030\001\004\001\005\001\006\001\007\001\255\255\255\255\255\255\
\255\255\012\001\255\255\014\001\015\001\016\001\255\255\018\001\
\019\001\255\255\021\001\255\255\023\001\255\255\025\001\026\001\
\027\001\255\255\029\001\030\001\004\001\005\001\006\001\007\001\
\255\255\255\255\255\255\255\255\012\001\255\255\014\001\015\001\
\016\001\255\255\018\001\019\001\255\255\021\001\255\255\023\001\
\255\255\025\001\026\001\027\001\255\255\029\001\030\001\004\001\
\005\001\255\255\255\255\255\255\255\255\255\255\255\255\012\001\
\255\255\014\001\015\001\016\001\255\255\018\001\019\001\255\255\
\021\001\255\255\023\001\255\255\025\001\026\001\027\001\255\255\
\029\001"

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
# 339 "parser.ml"
               : Syntax.command))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 41 "parser.mly"
                      ( CExp(_1) )
# 346 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 42 "parser.mly"
                                   ( CLet(_2,_4) )
# 354 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'vars) in
    Obj.repr(
# 43 "parser.mly"
                                (CLet(_2,_3))
# 362 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'ands) in
    Obj.repr(
# 44 "parser.mly"
                                            ( CRLet ((_3,_4,_6)::_7) )
# 372 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'var) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'vars) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'ands) in
    Obj.repr(
# 45 "parser.mly"
                                         ( CRLet((_3,_4,_5)::_6) )
# 382 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    Obj.repr(
# 46 "parser.mly"
        ( EoF )
# 388 "parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "parser.mly"
          ([])
# 394 "parser.ml"
               : 'ands))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'var) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'ands) in
    Obj.repr(
# 51 "parser.mly"
                             ( (_2,_3,_5)::_6 )
# 404 "parser.ml"
               : 'ands))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 55 "parser.mly"
                ( EFun (_1,_3) )
# 412 "parser.ml"
               : 'vars))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'vars) in
    Obj.repr(
# 56 "parser.mly"
             ( EFun (_1,_2) )
# 420 "parser.ml"
               : 'vars))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 60 "parser.mly"
                                    ( EFun (_1,_3) )
# 428 "parser.ml"
               : 'varf))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'varf) in
    Obj.repr(
# 61 "parser.mly"
                                    ( EFun (_1,_2) )
# 436 "parser.ml"
               : 'varf))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 65 "parser.mly"
                              ( EFun (_2,_4) )
# 444 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'varf) in
    Obj.repr(
# 66 "parser.mly"
                              ( EFun (_2,_3) )
# 452 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 6 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 5 : 'var) in
    let _6 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'ands) in
    let _9 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 67 "parser.mly"
                                         ( ERLet((_3,_4,_6)::_7,_9) )
# 463 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'vars) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'ands) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 68 "parser.mly"
                                      ( ERLet((_3,_4,_5)::_6,_8) )
# 474 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 69 "parser.mly"
                                  ( ELet(_2,_4,_6) )
# 483 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'vars) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 70 "parser.mly"
                             (ELet(_2,_3,_5))
# 492 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 71 "parser.mly"
                                 ( EIf(_2,_4,_6) )
# 501 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'pattern_and_expr) in
    Obj.repr(
# 72 "parser.mly"
                                         ( EMatch(_2,_4) )
# 509 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'eq_lt_expr) in
    Obj.repr(
# 73 "parser.mly"
                              ( _1 )
# 516 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 77 "parser.mly"
                               ( [(_1,_3)] )
# 524 "parser.ml"
               : 'pattern_and_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'pattern_and_expr) in
    Obj.repr(
# 78 "parser.mly"
                                             ( (_1,_3)::_5 )
# 533 "parser.ml"
               : 'pattern_and_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_tupl_pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'pattern) in
    Obj.repr(
# 82 "parser.mly"
                                     ( PLCons(_1,_3) )
# 541 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'list_tupl_pattern) in
    Obj.repr(
# 83 "parser.mly"
                             ( _1 )
# 548 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'p_tuple_elements) in
    Obj.repr(
# 87 "parser.mly"
                                ( _2 )
# 555 "parser.ml"
               : 'list_tupl_pattern))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'p_list_elements) in
    Obj.repr(
# 88 "parser.mly"
                                      ( _2 )
# 562 "parser.ml"
               : 'list_tupl_pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_pattern) in
    Obj.repr(
# 89 "parser.mly"
                                   ( _1 )
# 569 "parser.ml"
               : 'list_tupl_pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'pattern) in
    Obj.repr(
# 93 "parser.mly"
                          ( PTCons(_1,PTCons(_3,PNil)) )
# 577 "parser.ml"
               : 'p_tuple_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'p_tuple_elements) in
    Obj.repr(
# 94 "parser.mly"
                                    ( PTCons(_1,_3) )
# 585 "parser.ml"
               : 'p_tuple_elements))
; (fun __caml_parser_env ->
    Obj.repr(
# 98 "parser.mly"
                         ( PNil )
# 591 "parser.ml"
               : 'p_list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'p_list_elements) in
    Obj.repr(
# 99 "parser.mly"
                                       ( PLCons(_1,_3) )
# 599 "parser.ml"
               : 'p_list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'pattern) in
    Obj.repr(
# 100 "parser.mly"
            ( PLCons(_1,PNil) )
# 606 "parser.ml"
               : 'p_list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 104 "parser.mly"
               ( PInt(_1) )
# 613 "parser.ml"
               : 'atomic_pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 105 "parser.mly"
               ( PBool(_1) )
# 620 "parser.ml"
               : 'atomic_pattern))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'pattern) in
    Obj.repr(
# 106 "parser.mly"
                      ( _2 )
# 627 "parser.ml"
               : 'atomic_pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 107 "parser.mly"
               ( PVar(_1) )
# 634 "parser.ml"
               : 'atomic_pattern))
; (fun __caml_parser_env ->
    Obj.repr(
# 108 "parser.mly"
               ( PUnder )
# 640 "parser.ml"
               : 'atomic_pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'eq_lt_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cons_expr) in
    Obj.repr(
# 112 "parser.mly"
                              ( EBin(OpEq,_1,_3) )
# 648 "parser.ml"
               : 'eq_lt_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'eq_lt_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cons_expr) in
    Obj.repr(
# 113 "parser.mly"
                              ( EBin(OpLt,_1,_3) )
# 656 "parser.ml"
               : 'eq_lt_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'cons_expr) in
    Obj.repr(
# 114 "parser.mly"
                  ( _1 )
# 663 "parser.ml"
               : 'eq_lt_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cons_expr) in
    Obj.repr(
# 118 "parser.mly"
                                ( EBin(OpCons,_1,_3) )
# 671 "parser.ml"
               : 'cons_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arith_expr) in
    Obj.repr(
# 119 "parser.mly"
                   ( _1 )
# 678 "parser.ml"
               : 'cons_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 123 "parser.mly"
                                  ( EBin(OpAdd,_1,_3) )
# 686 "parser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 124 "parser.mly"
                                   ( EBin(OpSub,_1,_3) )
# 694 "parser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 125 "parser.mly"
                                ( _1 )
# 701 "parser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'factor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'fapp_expr) in
    Obj.repr(
# 129 "parser.mly"
                                  ( EBin(OpMul,_1,_3) )
# 709 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'factor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'fapp_expr) in
    Obj.repr(
# 130 "parser.mly"
                                ( EBin(OpDiv,_1,_3) )
# 717 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'factor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'fapp_expr) in
    Obj.repr(
# 131 "parser.mly"
                                ( EBin(OpMod,_1,_3) )
# 725 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fapp_expr) in
    Obj.repr(
# 132 "parser.mly"
                              ( _1 )
# 732 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'fapp_expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'list_tuple_expr) in
    Obj.repr(
# 136 "parser.mly"
                                    ( EApp (_1,_2) )
# 740 "parser.ml"
               : 'fapp_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'list_tuple_expr) in
    Obj.repr(
# 137 "parser.mly"
                                    ( _1 )
# 747 "parser.ml"
               : 'fapp_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'tuple_elements) in
    Obj.repr(
# 141 "parser.mly"
                              ( _2 )
# 754 "parser.ml"
               : 'list_tuple_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'list_elements) in
    Obj.repr(
# 142 "parser.mly"
                                    ( _2 )
# 761 "parser.ml"
               : 'list_tuple_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_expr) in
    Obj.repr(
# 143 "parser.mly"
                                ( _1 )
# 768 "parser.ml"
               : 'list_tuple_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 147 "parser.mly"
                               ( ETCons(_1,ETCons(_3,ENil)) )
# 776 "parser.ml"
               : 'tuple_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tuple_elements) in
    Obj.repr(
# 148 "parser.mly"
                               ( ETCons(_1,_3) )
# 784 "parser.ml"
               : 'tuple_elements))
; (fun __caml_parser_env ->
    Obj.repr(
# 152 "parser.mly"
                         ( ENil )
# 790 "parser.ml"
               : 'list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_elements) in
    Obj.repr(
# 153 "parser.mly"
                                  ( ELCons(_1,_3) )
# 798 "parser.ml"
               : 'list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 154 "parser.mly"
         ( ELCons(_1,ENil) )
# 805 "parser.ml"
               : 'list_elements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 158 "parser.mly"
                   ( EValue (VInt _1) )
# 812 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 159 "parser.mly"
                   ( EValue (VBool _1) )
# 819 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 160 "parser.mly"
                   ( _2 )
# 826 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 161 "parser.mly"
         ( EVar (_1) )
# 833 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 165 "parser.mly"
        ( _1 )
# 840 "parser.ml"
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
