open Syntax
open Evaluation
open Typesystem
open Parser
open Lexer

let rec string_of_value : value -> string = fun v ->
  match v with
    VInt i -> string_of_int i
  | VBool b -> string_of_bool b
  | VFun (nm,e,ev) -> "<fun>"
  | VRFun _ -> "<fun>"
  | VTCons _ -> "("^string_of_tuple v
  | VLCons _ -> "["^string_of_list v
  | VNil -> "[]"

and string_of_tuple : value -> string = fun x ->
  match x with
    VNil -> "\b\b)"
  | VTCons(x,rest) -> string_of_value x ^ ", " ^ string_of_tuple rest
  |  _ -> failwith __LOC__

and string_of_list : value -> string = fun x ->
  match x with
    VNil -> "\b\b]"
  | VLCons(x,rest) -> string_of_value x ^ "; " ^ string_of_list rest
  |  _ -> failwith __LOC__

let rec string_of_type : ty -> string = fun v ->
  match v with
    TyInt -> "int"
  | TyBool -> "bool"
  | TyArr (ty1,ty2) -> "("^(string_of_type ty1)^" -> "^(string_of_type ty2)^")"
  | TyId x -> "'"^x
  | TyList t -> (string_of_type t)^" list"
  | TyTuple tlist -> string_of_tlist tlist

and string_of_tlist : ty list -> string = fun tlist ->
  match tlist with
    [] -> "\b\b"
  | t::rest -> string_of_type t ^ " * " ^ string_of_tlist rest

let print_value : value -> unit = fun v -> 
  print_string (string_of_value v)

let print_type : ty -> unit = fun t ->
  print_string (string_of_type t)

let rec print_command_result : command_result -> ty list -> unit = fun result t->
  match result with
    Command_result (None,v,ev) -> print_string("- : ");
    List.iter print_type t;
    print_string(" = ");
    List.iter print_value v;print_newline()
  | Command_result (Some env',v,ev) 
    -> try
      List.iter2 (fun t' x -> print_string ("val "^(fst x)^" : ");print_type t';print_string(" = ");print_value (snd x);print_newline()) t env'
    with Invalid_argument _ -> ()
