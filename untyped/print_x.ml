open Syntax
open Evaluation
open Parser
open Lexer

let rec string_of_value : value -> string = fun v ->
  match v with
    VInt i -> "int = "^string_of_int i
  | VBool b -> "bool = "^string_of_bool b
  | VFun (nm,e,ev) -> "<fun>"
  | VRFun _ -> "<fun>(再帰)"
  | VTCons _ -> "tuple = ( "^string_of_tuple v
  | VLCons _ -> "list = [ "^string_of_list v
  | VNil -> "list = []"

and string_of_tuple : value -> string = fun x ->
  match x with
    VNil -> "\b\b)"
  | VTCons(x,rest) -> string_of_value x ^ " , " ^ string_of_tuple rest
  |  _ -> failwith __LOC__

and string_of_list : value -> string = fun x ->
  match x with
    VNil -> "\b\b]"
  | VLCons(x,rest) -> string_of_value x ^ " ; " ^ string_of_list rest
  |  _ -> failwith __LOC__

let print_value : value -> unit = fun v -> 
  print_string (string_of_value v)

let rec print_command_result : command_result -> unit = fun result ->
  match result with
    Command_result (None,v,ev) -> print_string("- : ");List.iter print_value v;print_newline()
  | Command_result (Some env',v,ev) 
    -> List.iter (fun x -> print_string ("val "^(fst x)^" : ");print_value (snd x);print_newline()) env'
