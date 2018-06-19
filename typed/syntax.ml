type name = string 

type binOp = OpAdd | OpSub | OpMul | OpDiv | OpMod | OpEq | OpLt | OpCons

type pattern = PInt of int | PBool of bool | PVar of name
             | PNil (* タプル／リスト共用の終端記号 *)
             | PTCons of pattern * pattern (* タプル *)
             | PLCons of pattern * pattern (* リスト *)
             | PUnder

and value = VInt of int | VBool of bool
          | VFun of name * expr * env
          | VRFun of name * (name * name * expr) list * env
          | VNil
          | VTCons of value * value 
          | VLCons of value * value 

and expr = EValue of value
         | EVar   of name
         | EBin of binOp * expr * expr 
         | ELet of pattern * expr * expr 
         | EIf of expr * expr * expr
         | EFun of name * expr
         | ERLet of (name * name * expr) list * expr
         | EApp of expr * expr
         | EMatch of expr * (pattern * expr) list
         | ENil 
         | ETCons of expr * expr
         | ELCons of expr * expr

and env = (name * value) list

type command = CExp of expr 
             | CLet of pattern * expr 
             | CRLet of (name * name * expr) list
             | EoF

exception Eval_error of string
exception Match_failure_1 of string

