open Syntax
open Util

type tyName = string

type ty = TyInt | TyBool | TyArr of ty * ty | TyId of tyName | TyList of ty | TyTuple of ty list

type ty_subst = (tyName * ty) list

type ty_constraints = (ty * ty) list

type ty_env = (name * ty) list

exception Type_error of string

let rec tlist_to_constraints : ty list -> ty_constraints = fun tlist ->
  match tlist with
    [] -> []
  | a::b::rest -> (a,b)::tlist_to_constraints (b::rest)
  | a::[] -> []

let rec ty_tylist_to_c : ty -> ty list -> ty_constraints = fun t -> fun tlist ->
  match tlist with
    [] -> []
  | a::rest -> (t,a)::ty_tylist_to_c t rest

let rec pattern_ty_to_env : pattern -> ty -> ty_env = fun p -> fun t ->
  match p,t with
    PNil ,_ -> []
  | PInt _,_ -> []
  | PBool _,_ -> []
  | PUnder ,_ -> []
  | PVar x,t -> [(x,t)]
  | PTCons (x,xrest),TyTuple tlist -> 
    pattern_ty_to_env x (List.hd tlist)@pattern_ty_to_env xrest (TyTuple(List.tl tlist))
  | PLCons (x,xrest),TyList t -> 
    pattern_ty_to_env x t@pattern_ty_to_env xrest (TyList t)
  | _ -> []


let rec apply_ty_subst : ty_subst -> ty -> ty = fun tysb -> fun ty1 ->
  match ty1 with
    TyInt -> TyInt
  | TyBool -> TyBool
  | TyArr (t1,t2) -> TyArr (apply_ty_subst tysb t1,apply_ty_subst tysb t2)
  | TyId t ->
    begin
      match List.assoc_opt t tysb with
        Some x -> x
      | None -> ty1
    end
  | TyList t -> TyList (apply_ty_subst tysb t)
  | TyTuple tlist -> TyTuple (List.map (apply_ty_subst tysb) tlist)

let compose_ty_subst : ty_subst -> ty_subst -> ty_subst = fun tysb1 -> fun tysb2 ->
  let rec f1 : ty_subst -> ty_subst -> ty_subst = fun tysb1 -> fun tysb2 ->
    match tysb2 with
      [] -> []
    | (tyname,t)::rest -> (tyname,apply_ty_subst tysb1 t)::f1 tysb1 rest
  and f2 : ty_subst -> ty_subst -> ty_subst = fun tysb1 -> fun tysb2 ->
    match tysb1 with
      [] -> []
    | (tyname,t)::rest ->
      match List.assoc_opt tyname tysb2 with
        Some x -> f2 rest tysb2
      | None -> (tyname,t)::f2 rest tysb2
  in (f1 tysb1 tysb2)@(f2 tysb1 tysb2)

let rec appearance_inspection :tyName -> ty -> bool = fun x -> fun t ->
  match t with
    TyId a -> if a = x then true else false
  | TyArr (a,b) -> appearance_inspection x a || appearance_inspection x b
  | TyList t1 -> appearance_inspection x t1
  | TyTuple tlist -> List.exists (appearance_inspection x) tlist
  | _ -> false

let rec ty_unify : ty_constraints -> ty_subst = fun c ->
  let rec f:tyName -> ty -> ty_constraints -> ty_constraints = fun x -> fun t -> fun c ->
    let rec g:ty -> ty-> ty = fun a -> fun b ->
      match a with
        TyId x' when x' = x -> b
      | TyArr (t1,t2) -> TyArr(g t1 t,g t2 t) 
      | TyList t1 -> TyList (g t1 t)
      | TyTuple tlist -> TyTuple (List.map (fun ti -> g ti t) tlist)
      | a -> a
    in
    match c with
      [] -> []
    | (ty1,ty2)::rest -> (g ty1 t,g ty2 t)::f x t rest
  in
  match c with
    [] -> []
  | (s,t)::c' when s = t -> ty_unify c'
  | (TyId x,t)::c' -> if appearance_inspection x t then 
      failwith __LOC__
    else
      compose_ty_subst (ty_unify (f x t c')) [(x,t)]
  | (s,TyId x)::c' -> if appearance_inspection x s then 
      failwith __LOC__
    else
      compose_ty_subst (ty_unify (f x s c')) [(x,s)]
  | (TyArr (s1,s2), TyArr (t1,t2))::c' -> ty_unify (c'@[(s1,t1);(s2,t2)])
  | (TyList s,TyList t)::c' -> ty_unify (c'@[(s,t)])
  | (TyTuple slist,TyTuple tlist)::c' -> 
    let rec tytuples_to_c : ty list -> ty list -> ty_constraints = fun s -> fun t -> 
      begin
        match s,t with
          [],[] -> []
        | s::slist,t::tlist -> (s,t)::tytuples_to_c slist tlist
        | _ -> failwith (__LOC__)
      end
    in ty_unify (c'@tytuples_to_c slist tlist)
  | _ -> raise (Type_error __LOC__)

let counter = ref 0
let new_ty_var : unit -> tyName = fun () -> incr counter;string_of_int !counter

let rec gather_ty_constraints : ty_env -> expr -> ty * ty_constraints = fun tenv -> fun e ->
  match e with
    EValue VInt _ -> (TyInt,[])
  | EValue VBool _ -> (TyBool,[])
  | EBin (op,e1,e2) -> let (t1,c1) = gather_ty_constraints tenv e1 in
    let (t2,c2) = gather_ty_constraints tenv e2 in
    begin
      match op,t1,t2 with
        OpAdd,_,_ -> (TyInt,(t1,TyInt)::(t2,TyInt)::c1@c2)
      | OpSub,_,_ -> (TyInt,(t1,TyInt)::(t2,TyInt)::c1@c2)
      | OpMul,_,_ -> (TyInt,(t1,TyInt)::(t2,TyInt)::c1@c2)
      | OpDiv,_,_ -> (TyInt,(t1,TyInt)::(t2,TyInt)::c1@c2)
      | OpMod,_,_ -> (TyInt,(t1,TyInt)::(t2,TyInt)::c1@c2)
      | OpLt,_,_ -> (TyBool,(t1,TyInt)::(t2,TyInt)::c1@c2)
      | OpEq,_,_ -> (TyBool,(t1,t2)::c1@c2)
      | OpCons,ty1,_ -> let alpha = new_ty_var () in
        (TyList (TyId alpha),(ty1,TyId alpha)::c1@c2)
      | _-> failwith ("未実装"^__LOC__)
    end
  | EVar x -> 
    begin
      match List.assoc_opt x tenv with
        Some a -> (a,[])
      | None -> failwith ("Unbound value "^x)
    end
  | ELet (p,e1,e2) -> 
    let (t1,c1) = gather_ty_constraints tenv e1 in
    let (t2,c2) = gather_ty_constraints ((pattern_ty_to_env p t1)@tenv) e2 in
    (t2,c1@c2)
  | EIf (e1,e2,e3) -> let (t1,c1) = gather_ty_constraints tenv e1 in
    let (t2,c2) = gather_ty_constraints tenv e2 in
    let (t3,c3) = gather_ty_constraints tenv e3 in
    (t2,(t1,TyBool)::(t2,t3)::c1@c2@c3)
  | EFun (x,e) -> let alpha = new_ty_var () in 
    let (t,c) = gather_ty_constraints ((x,TyId alpha)::tenv) e in
    (TyArr (TyId alpha,t),c)
  | EApp (e1,e2) -> let (t1,c1) = gather_ty_constraints tenv e1 in
    let (t2,c2) = gather_ty_constraints tenv e2 in
    let alpha = new_ty_var () in 
    (TyId alpha,(t1,TyArr (t2,TyId alpha))::c1@c2)
  | ELCons (e1,e2) ->
    let (t1,c1) = gather_ty_constraints tenv e1 
    in let (t2,c2) = gather_ty_constraints tenv e2
    in (TyList t1,(TyList t1,t2)::c1@c2)
  | ENil -> let alpha = new_ty_var () in (TyList (TyId alpha),[])
  | ETCons (e1,e2) -> 
    let rec make_tclist tpl = 
      begin
        match tpl with
          ENil -> []
        | ETCons (e1,e2) -> gather_ty_constraints tenv e1::make_tclist e2
        | _ -> failwith __LOC__
      end
    in let lst = make_tclist e 
    in (TyTuple (fst (List.split lst)),List.concat(snd (List.split lst)))
  | ERLet (lst,e) -> 
    let rec make_exi l =
      match l with
        [] -> []
      | (fi,xi,exi)::rest -> exi::make_exi rest
    in
    let rec make_var l=
      match l with
        [] -> []
      | (fi,xi,exi)::rest -> TyArr(TyId (new_ty_var()),TyId (new_ty_var()))::make_var rest
    in
    let rec make_tenv1 l1 l2 =
      match l1,l2 with
        [],[] -> []
      | (fi,xi,exi)::rest1,tyarr::rest2 -> (fi,tyarr)::make_tenv1 rest1 rest2
      | _ -> failwith __LOC__
    in
    let rec make_tenv2 l1 l2 =
      match l1,l2 with
        [],[] -> []
      | (fi,xi,exi)::rest1,TyArr(a,b)::rest2 -> (xi,a)::make_tenv2 rest1 rest2
      | _ -> failwith __LOC__
    in let varlist = make_var lst
    in let tenv1' = (make_tenv1 lst varlist)@tenv
    in let tenv2' = (make_tenv2 lst varlist)@tenv1'
    in let tc = List.map (gather_ty_constraints tenv2') (make_exi lst)
    in 
    let rec make_tibeta l1 l2=
      match l1,l2 with
        [],[] -> []
      | (ti,ci)::rest1,TyArr(a,b)::rest2 -> (ti,b)::make_tibeta rest1 rest2
      | _ -> failwith __LOC__
    in let ci = make_tibeta tc varlist
    in let (t2,c2) = gather_ty_constraints tenv1' e in
    (t2,ci@List.concat(snd(List.split(tc)))@c2)
  | EMatch (e,pelist) -> let (t',c') = gather_ty_constraints tenv e 
    in let (plist,elist) = List.split pelist
    in let teclist = List.map gather_ty_constraints_pattern plist
    in let tylist = split_and_fst3 teclist
    in let t_t'_c = ty_tylist_to_c t' tylist
    in let env' = List.concat (split_and_snd3 teclist)
    in let (tlist,clist) = List.split (List.map (gather_ty_constraints (env'@tenv)) elist)
    in let t_to_c = tlist_to_constraints tlist
    in (List.hd tlist,t_t'_c@t_to_c@List.concat clist)
  | _ -> failwith ("未実装"^__LOC__)

and gather_ty_constraints_pattern : pattern -> ty * ty_env * ty_constraints = fun p ->
  match p with
    PInt _ -> (TyInt,[],[])
  | PBool _ -> (TyBool,[],[])
  | PVar x -> let alpha = TyId (new_ty_var ()) in (alpha,[(x,alpha)],[])
  | PNil -> let alpha = new_ty_var () in (TyList (TyId alpha),[],[])
  | PTCons (a,arest) ->
    let rec make_ty tpl = 
      begin
        match tpl with
          PNil -> []
        | PTCons (a,arest) -> (gather_ty_constraints_pattern a)::make_ty arest
        | _ -> failwith __LOC__
      end
    in let lst = make_ty p
    in (TyTuple (split_and_fst3 lst),List.concat(split_and_snd3 lst),List.concat(split_and_trd3 lst))
  | PLCons (a,arest) ->
    let (t1,tenv1,c1) = gather_ty_constraints_pattern a 
    in let (t2,tenv2,c2) = gather_ty_constraints_pattern arest
    in (TyList t1,tenv1@tenv2,(TyList t1,t2)::c1@c2)
  | PUnder -> (TyId (new_ty_var ()),[],[])

let rec infer_expr : ty_env -> expr -> ty * ty_env = fun tenv -> fun e ->
  let (t,c)= gather_ty_constraints tenv e in 
  let ts = ty_unify c
  in (apply_ty_subst ts t ,List.map (fun (x,y) -> (x,apply_ty_subst ts y)) tenv)

let rec infer_cmd : ty_env -> command -> ty list * ty_env = fun tenv -> fun com ->
  match com with
    CExp e -> let (t,new_ty_env) = infer_expr tenv e in ([t],new_ty_env)
  | CLet (p,e) -> let (t,new_ty_env)= infer_expr tenv e in 
    let tenv' = (pattern_ty_to_env p t) in (snd (List.split tenv'),tenv'@new_ty_env)
  | CRLet lst -> 
    let rec make_exi l =
      match l with
        [] -> []
      | (fi,xi,exi)::rest -> exi::make_exi rest
    in
    let rec make_var l=
      match l with
        [] -> []
      | (fi,xi,exi)::rest -> TyArr(TyId (new_ty_var()),TyId (new_ty_var()))::make_var rest
    in
    let rec make_tenv1 l1 l2 =
      match l1,l2 with
        [],[] -> []
      | (fi,xi,exi)::rest1,tyarr::rest2 -> (fi,tyarr)::make_tenv1 rest1 rest2
      | _ -> failwith __LOC__
    in
    let rec make_tenv2 l1 l2 =
      match l1,l2 with
        [],[] -> []
      | (fi,xi,exi)::rest1,TyArr(a,b)::rest2 -> (xi,a)::make_tenv2 rest1 rest2
      | _ -> failwith __LOC__
    in let varlist = make_var lst
    in let tenv1' = (make_tenv1 lst varlist)@tenv
    in let tenv2' = (make_tenv2 lst varlist)@tenv1'
    in let tc = List.map (gather_ty_constraints tenv2') (make_exi lst)
    in 
    let rec make_tibeta l1 l2=
      match l1,l2 with
        [],[] -> []
      | (ti,ci)::rest1,TyArr(a,b)::rest2 -> (ti,b)::make_tibeta rest1 rest2
      | _ -> failwith __LOC__
    in let ci = make_tibeta tc varlist
    in let ts = ty_unify (ci@List.concat(snd(List.split(tc))))
    in let lst = List.map (fun (x,y) -> (x,apply_ty_subst ts y)) tenv1'
    in (snd (List.split lst),List.map (fun (x,y) -> (x,apply_ty_subst ts y)) tenv2')
  | EoF -> raise End_of_file

