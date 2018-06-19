open Syntax
open Parser
open Lexer

exception No_value

let get aopt = 
  match aopt with
    Some a -> a
  | None -> raise No_value

let moveopt lst = 
  let rec moveopt' lst' = 
    match lst' with
      [] -> []
    | (Some x)::rest -> x @ moveopt' rest
    | None::rest -> raise No_value
  in try Some (moveopt' lst) with No_value -> None

let rec nth_name lst name = 
  match lst with
    [] -> raise (Failure "nth_name")
  | (fi,xi,exi)::rest -> if fi = name then (fi,xi,exi) else nth_name rest name

let hd_p lst =
  match lst with
    PLCons(x,xrest) -> x
  | PTCons(x,xrest) -> x
let tl_p lst =
  match lst with
    PLCons(x,xrest) -> xrest
  | PTCons(x,xrest) -> xrest

let hd_v lst = 
  match lst with
    VLCons(x,xrest) -> x
  | VTCons(x,xrest) -> x
let tl_v lst = 
  match lst with
    VLCons(x,xrest) -> xrest
  | VTCons(x,xrest) -> xrest

let rec plength cons = 
  match cons with
    PNil -> 0 
  | PTCons(x,rest) -> 1 + plength rest
  | PLCons(x,rest) -> 1 + plength rest
  | _ -> 1

let rec vlength cons = 
  match cons with
    VNil -> 0 
  | VTCons(x,rest) -> 1 + vlength rest
  | VLCons(x,rest) -> 1 + vlength rest
  | _ -> 1