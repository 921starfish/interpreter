open Syntax
open Evaluation
open Print_x
open Parser
open Lexer

let rec repl: env -> unit = fun ev -> 
  print_string "# ";
  flush stdout;
  try
    let lexbuf = Lexing.from_channel stdin in
    let result = com_to_result ev (Parser.main Lexer.token lexbuf) in
    print_command_result result;
    repl (env_of_result result)
  with Syntax.Match_failure_1 _ -> print_endline (__LOC__^":マッチ失敗");repl ev


let rec file: Lexing.lexbuf -> env -> unit = fun lexbuf ev -> 
  let result = com_to_result ev (Parser.main Lexer.token lexbuf) in
  print_command_result result;
  file lexbuf (env_of_result result)

let rec s_to_l = function
    [] -> []
  | x::xs -> Lexing.from_string x::s_to_l xs

let main () =
  try 
    if Array.length Sys.argv = 1 then (* REPLのとき *)
      repl []
    else (* ファイルを読む時 *)
      let ic = open_in Sys.argv.(1) in
      let lexbuf = Lexing.from_channel ic in
      try
        file lexbuf []
      with End_of_file -> close_in ic
  with 
  | Parsing.Parse_error -> 
    print_endline (__LOC__^":Parse Error!")

;;
if !Sys.interactive then 
  ()
else 
  main ()



