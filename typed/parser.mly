%{
  open Syntax
  (* ここに書いたものは，ExampleParser.mliに入らないので注意 *)
%}

%token <int>    INT
%token <bool>   BOOL
%token <string> ID 
%token EQ
%token LT
%token PLUS 
%token MINUS
%token TIMES 
%token DIV
%token MOD
%token LPAR RPAR 
%token LBRACKET RBRACKET
%token COMMA
%token SEMICOLON
%token IF THEN ELSE 
%token LET IN
%token REC
%token AND
%token MATCH WITH BAR END
%token UNDER
%token DSEMICOLON
%token DCOLON
%token FUN
%token RARROW
%token EOF

%start main 
%type <Syntax.command> main
%% 

main: 
  | command { $1 }
;

command:   
  | expr DSEMICOLON   { CExp($1) }
  | LET pattern EQ expr DSEMICOLON { CLet($2,$4) }
  | LET pattern vars DSEMICOLON {CLet($2,$3)}
  | LET REC var var EQ expr ands DSEMICOLON { CRLet (($3,$4,$6)::$7) }
  | LET REC var var vars ands DSEMICOLON { CRLet(($3,$4,$5)::$6) }
  | EOF { EoF }
;

ands:
  |       {[]}
  | AND var var EQ expr ands { ($2,$3,$5)::$6 } 
;

vars:
  | var EQ expr { EFun ($1,$3) }
  | var vars { EFun ($1,$2) }
;

varf:
  | var RARROW expr                 { EFun ($1,$3) }
  | var varf                        { EFun ($1,$2) }
;
    
expr:
  | FUN var RARROW expr       { EFun ($2,$4) }
  | FUN var varf              { EFun ($2,$3) }
  | LET REC var var EQ expr ands IN expr { ERLet(($3,$4,$6)::$7,$9) }
  | LET REC var var vars ands IN expr { ERLet(($3,$4,$5)::$6,$8) }
  | LET pattern EQ expr IN expr   { ELet($2,$4,$6) }
  | LET pattern vars IN expr {ELet($2,$3,$5)}
  | IF expr THEN expr ELSE expr  { EIf($2,$4,$6) }
  | MATCH expr WITH pattern_and_expr END { EMatch($2,$4) }
  | eq_lt_expr                { $1 } 
;

pattern_and_expr:
  | pattern RARROW expr        { [($1,$3)] }
  | pattern RARROW expr BAR pattern_and_expr { ($1,$3)::$5 }
;

pattern:
  | list_tupl_pattern DCOLON pattern { PLCons($1,$3) }
  | list_tupl_pattern        { $1 }
;

list_tupl_pattern:
  | LPAR p_tuple_elements RPAR  { $2 }
  | LBRACKET p_list_elements RBRACKET { $2 }
  | atomic_pattern                 { $1 }
;

p_tuple_elements:
  | pattern COMMA pattern { PTCons($1,PTCons($3,PNil)) }
  | pattern COMMA p_tuple_elements  { PTCons($1,$3) }
;

p_list_elements:
  |                      { PNil }
  | pattern SEMICOLON p_list_elements  { PLCons($1,$3) }
  | pattern { PLCons($1,PNil) }
;

atomic_pattern:
  | INT        { PInt($1) }
  | BOOL       { PBool($1) }
  | LPAR pattern RPAR { $2 }
  | var        { PVar($1) }
  | UNDER      { PUnder }
;

eq_lt_expr:    
  | eq_lt_expr EQ cons_expr   { EBin(OpEq,$1,$3) }
  | eq_lt_expr LT cons_expr   { EBin(OpLt,$1,$3) }
  | cons_expr     { $1 }
;

cons_expr:
  | arith_expr DCOLON cons_expr { EBin(OpCons,$1,$3) }
  | arith_expr     { $1 }
;

arith_expr:
  | arith_expr PLUS factor_expr   { EBin(OpAdd,$1,$3) }
  | arith_expr MINUS factor_expr   { EBin(OpSub,$1,$3) }
  | factor_expr                 { $1 }
;

factor_expr:
  | factor_expr TIMES fapp_expr   { EBin(OpMul,$1,$3) }
  | factor_expr DIV fapp_expr   { EBin(OpDiv,$1,$3) }
  | factor_expr MOD fapp_expr   { EBin(OpMod,$1,$3) }
  | fapp_expr                 { $1 }
;

fapp_expr:
  | fapp_expr list_tuple_expr       { EApp ($1,$2) }
  | list_tuple_expr                 { $1 }
;

list_tuple_expr:
  | LPAR tuple_elements RPAR  { $2 }
  | LBRACKET list_elements RBRACKET { $2 }
  | atomic_expr                 { $1 }
;

tuple_elements:
  | expr COMMA expr            { ETCons($1,ETCons($3,ENil)) }
  | expr COMMA tuple_elements  { ETCons($1,$3) }
;

list_elements:
  |                      { ENil }
  | expr SEMICOLON list_elements  { ELCons($1,$3) }
  | expr { ELCons($1,ENil) }
;

atomic_expr:
  | INT            { EValue (VInt $1) }
  | BOOL           { EValue (VBool $1) }
  | LPAR expr RPAR { $2 }
  | var  { EVar ($1) } 
;

var:
  | ID  { $1 } 
;

