open Syntax
open Util

type command_result = Command_result of env option * (value list) * env

let chouhuku_check : pattern -> bool = fun p ->
  let rec make_stack :pattern -> name list = fun p' ->
    match p' with
      PVar x -> [x]
    | PTCons (a,arest) -> make_stack a@make_stack arest
    | PLCons (a,arest) -> make_stack a@make_stack arest
    | _ -> []
  in duplication_check (make_stack p)

let rec find_match : pattern -> value -> env option = fun p v ->
  match p,v with
    PInt pi,VInt vi -> if vi = pi then Some [] else None
  | PBool pb,VBool vb -> if vb = pb then Some [] else None
  | PTCons (a,arest),VTCons (v,vrest) -> if chouhuku_check p then failwith "bound several times" 
    else moveopt ((find_match a v)::[find_match arest vrest])
  | PLCons (a,arest),VLCons (v,vrest) -> if chouhuku_check p then failwith "bound several times" 
    else moveopt ((find_match a v)::[find_match arest vrest])
  | PNil,VNil -> Some []
  | PNil,_ -> None
  | PVar px,v -> Some [(px,v)]
  | PUnder,v -> Some [("\b\b\b\b-",v)]
  | _ -> None

let rec binopelation :binOp -> value -> value -> value = fun op v1 v2 ->
  match op,v1,v2 with
    OpAdd,(VInt i1),(VInt i2) -> VInt(i1+i2)
  | OpSub,(VInt i1),(VInt i2) -> VInt(i1-i2)
  | OpMul,(VInt i1),(VInt i2) -> VInt(i1*i2)
  | OpDiv,(VInt i1),(VInt i2) -> VInt(i1/i2)
  | OpMod,(VInt i1),(VInt i2) -> VInt(i1 mod i2)
  | OpLt,(VInt i1),(VInt i2) -> VBool(i1<i2)
  | OpEq,(VInt i1),(VInt i2) -> VBool(i1=i2)
  | OpEq,(VBool b1),(VBool b2) -> VBool(b1=b2)
  | OpEq,(VTCons _),(VTCons _) -> 
    let rec eq aconf bconf = 
      match aconf,bconf with
        VNil,VNil -> VBool true
      | VTCons(a,arest),VTCons(b,brest) -> 
        if binopelation OpEq a b = VBool true then eq arest brest else VBool false
      | _ -> raise (Eval_error (__LOC__)) 
    in if vlength v1 = vlength v2 then eq v1 v2 else VBool false
  | OpEq,(VLCons _),(VLCons _ ) ->
    let rec eq aconf bconf = 
      match aconf,bconf with
        VNil,VNil -> VBool true
      | VLCons(a,arest),VLCons(b,brest) -> 
        if binopelation OpEq a b = VBool true then eq arest brest else VBool false
      | _ -> raise (Eval_error (__LOC__)) 
    in if vlength v1 = vlength v2 then eq v1 v2 else VBool false
  | OpCons,v1,(VLCons _)
  | OpCons,v1,VNil -> VLCons (v1,v2)
  | _ -> raise (Eval_error (__LOC__^":２項演算エラー"))

let rec if_ :value -> env-> expr -> expr -> value = fun v1 ev e2 e3->
  match v1 with
    (VBool true) -> eval ev e2
  | (VBool false) -> eval ev e3
  | _ -> raise (Eval_error (__LOC__^":if文の条件式が整数"))

and eval : env -> expr -> value = fun ev ex ->
  match ex with
    EValue v -> v
  | EVar x -> (try List.assoc x ev with Not_found -> failwith "変数")
  | ELet (p,e1,e2) -> eval ((get(find_match p (eval ev e1)))@ev) e2
  | EBin (op,e1,e2) -> binopelation op (eval ev e1) (eval ev e2)
  | EIf (e1,e2,e3) -> let v1 = (eval ev e1) in if_ v1 ev e2 e3 (*e2とe3の型違いはエラーはかない*)
  | EFun (x,e) -> VFun (x,e,ev)
  | ERLet (lst,e) ->
    let rec make_value l=
      match l with
        [] -> []
      | (fi,xi,exi)::rest -> (VRFun(fi,lst,ev))::make_value rest
    in 
    let rec make_env l1 l2 =
      match l1,l2 with
        [],[] -> []
      | (fi,xi,exi)::rest1,v::rest2 -> (fi,v)::make_env rest1 rest2
      | _ -> failwith __LOC__
    in let env' = make_env lst (make_value lst) in eval (env'@ev) e
  | EApp (e1,e2) ->
    let v1 = eval ev e1 in let v2 = eval ev e2 in
    begin
      match v1 with 
        VFun (x,e,oenv) -> eval ((x,v2)::oenv) e
      | VRFun (n,lst,oenv) -> let (_,x',e') = nth_name lst n in
        let rec make_value l=
          begin
            match l with
              [] -> []
            | (fi,xi,exi)::rest -> (VRFun(fi,lst,oenv))::make_value rest
          end
        in let rec make_env l1 l2 =
             begin
               match l1,l2 with
                 [],_ -> []
               | (fi,xi,exi)::rest1,v::rest2 -> (fi,v)::make_env rest1 rest2
               | _ -> failwith __LOC__
             end
        in let env'= (x',v2)::make_env lst (make_value lst) @oenv in eval env' e'
      | _ -> failwith (__LOC__^"エラー")
    end
  | EMatch (e,pelist)-> let v = (eval ev e) in find ev pelist v
  | ELCons _ | ETCons _ -> vcons_of_econs eval ev ex
  | ENil -> VNil

and find : env -> (pattern * expr) list -> value -> value = fun ev pelist v ->
  match pelist with
    [] -> raise (Match_failure_1 "マッチ失敗")
  | x::xs -> let ev' = find_match (fst x) v in
    match ev' with
      None -> find ev xs v
    | Some a -> eval (a@ev) (snd x)

and vcons_of_econs f e lst = 
  match lst with
    ENil -> VNil
  | ETCons (x,rest) -> VTCons (f e x, vcons_of_econs f e rest)
  | ELCons (x,rest) -> VLCons (f e x, vcons_of_econs f e rest)
  | _ -> failwith "ENilで終わってないCons"

let env_of_result = function
    Command_result (_,_,ev) -> ev

let rec com_to_result : env -> command -> command_result = fun ev com ->
  match com with
    CExp ex -> Command_result (None,[(eval ev ex)],ev)
  | CLet (p,ex) -> let a = (eval ev ex) in Command_result (find_match p a,[a],(get(find_match p a))@ev)
  | CRLet lst ->
    let rec make_value l=
      match l with
        [] -> []
      | (fi,xi,exi)::rest -> (VRFun(fi,lst,ev))::make_value rest
    in let rec make_env l1 l2 =
         match l1,l2 with
           [],[] -> []
         | (fi,xi,exi)::rest1,v::rest2 -> (fi,v)::make_env rest1 rest2
         | _ -> failwith __LOC__
    in let env' = make_env lst (make_value lst)
    in Command_result (Some env',make_value lst, env'@ev)
  | EoF -> raise End_of_file
(*この関数が環境を返すのは次への引数用*)



