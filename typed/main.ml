open Syntax
open Evaluation
open Typesystem
open Print_x
open Parser
open Lexer

let rec repl: ty_env -> env -> unit = fun tev -> fun ev -> 
  print_string "# ";
  flush stdout;
  try
    let lexbuf = Lexing.from_channel stdin in
    let com = Parser.main Lexer.token lexbuf in
    let tresult = infer_cmd tev com in
    let result = com_to_result ev com in
    print_command_result result (fst tresult);
    repl (snd tresult) (env_of_result result)
  with 
    Match_failure_1 _ -> print_endline (__LOC__^":マッチ失敗");repl tev ev
  | Type_error _ -> print_endline (__LOC__^":型エラー");repl tev ev

let rec file: Lexing.lexbuf -> ty_env -> env -> unit = fun lexbuf tev ev -> 
  let com = Parser.main Lexer.token lexbuf in
  let tresult = infer_cmd tev com in
  let result = com_to_result ev com in
  print_command_result result (fst tresult);
  file lexbuf (snd tresult) (env_of_result result)

let rec s_to_l = function
    [] -> []
  | x::xs -> Lexing.from_string x::s_to_l xs

let main () =
  try 
    if Array.length Sys.argv = 1 then (* REPLのとき *)
      repl [] []
    else (* ファイルを読む時 *)
      let ic = open_in Sys.argv.(1) in
      let lexbuf = Lexing.from_channel ic in
      try
        file lexbuf [] []
      with End_of_file -> close_in ic
  with 
  | Parsing.Parse_error -> 
    print_endline (__LOC__^":Parse Error!")

;;
if !Sys.interactive then 
  ()
else 
  main ()



