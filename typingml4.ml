exception Hoge
exception Fuga

type op = P | M | T | L
type typing = TyInt | TyBool | TyFun of typing * typing | TyList of typing
type exp =
    I of int
  | B of bool
  | X of string
  | Cal of op * exp * exp
  | If of exp * exp * exp
  | Let of string * exp * exp * typing (*e1の型を指定*)
  | Fun of string * exp
  | App of exp * exp * typing (*e2*)
  | LetRec of string * string * exp * exp * typing * typing (*y, e1*)
  | Nil
  | Cons of exp * exp
  | Match of exp * exp * string * string * exp * typing (*x*)

type env = (string * typing) list
type judgement = Typing of env * exp * typing

type derivation =
  | TInt of judgement
  | TBool of judgement
  | TIf of judgement * derivation * derivation * derivation
  | TPlus of judgement * derivation * derivation
  | TMinus of judgement * derivation * derivation
  | TTimes of judgement * derivation * derivation
  | TLt of judgement * derivation * derivation
  | TVar of judgement
  | TLet of judgement * derivation * derivation
  | TFun of judgement * derivation
  | TApp of judgement * derivation * derivation
  | TLetRec of judgement * derivation * derivation
  | TNil of judgement
  | TCons of judgement * derivation * derivation
  | TMatch of judgement * derivation * derivation * derivation

let string_cal op = match op with
    P -> "+"
  | M -> "-"
  | T -> "*"
  | L -> "<"

let rec string_exp e = match e with
    I i -> string_of_int i
  | B b -> string_of_bool b
  | X x -> x
  | Cal (op, e1, e2) -> begin match e1 with
      I _ | B _ | X _ -> string_exp e1
    | _ -> "(" ^ string_exp e1 ^ ")" end ^ " " ^ string_cal op ^ " " ^ begin match e2 with
      I _ | B _ | X _ -> string_exp e2
    | _ -> "(" ^ string_exp e2 ^ ")" end
  | If (e1, e2, e3) -> "if " ^ string_exp e1 ^ " then " ^ string_exp e2 ^ " else " ^ string_exp e3
  | Let (x, e1, e2, _) -> "let " ^ x ^ " = " ^ string_exp e1 ^ " in " ^ string_exp e2
  | Fun (x, e) -> "fun " ^ x ^ " -> " ^ string_exp e
  | App (e1, e2, _) -> begin match e1 with
      I _ | B _ | X _ -> string_exp e1
    | _ -> "(" ^ string_exp e1 ^ ")" end ^ " " ^ begin match e2 with
      I _ | B _ | X _ -> string_exp e2
    | _ -> "(" ^ string_exp e2 ^ ")" end
  | LetRec (x, y, e1, e2, _, _) -> "let rec " ^ x ^ " = fun " ^ y ^ " -> " ^ string_exp e1 ^ " in " ^ string_exp e2
  | Nil -> "[]"
  | Cons (e1, e2) -> begin match e1 with
      I _ | B _ | X _ -> string_exp e1
    | _ -> "(" ^ string_exp e1 ^ ")" end ^ " :: " ^ string_exp e2
  | Match (e1, e2, x, y, e3, _) -> "match " ^ string_exp e1 ^ " with [] -> " ^ string_exp e2 ^ " | " ^ x ^ " :: " ^ y ^ " -> " ^ string_exp e3

let rec string_type t = match t with
    TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1, t2) -> begin match t1 with
    | TyFun _ -> "(" ^ string_type t1 ^ ")"
    | _ -> string_type t1 end ^ " -> " ^ string_type t2
  | TyList t0 -> begin match t0 with
    | TyFun _ -> "(" ^ string_type t0 ^ ")"
    | _ -> string_type t0 end ^ " list"
let rec string_env env = match env with
    [] -> ""
  | [(x, t)] -> x ^ " : " ^ string_type t
  | (x, t) :: rest -> string_env rest ^ ", " ^ x ^ " : " ^ string_type t

let rec typing env e t = match e with
    I i -> TInt (Typing (env, e, TyInt))
  | B b -> TBool (Typing (env, e, TyBool))
  | X x -> begin match env with
      [] -> raise Hoge
    | (x0, t0) :: rest -> if x = x0 then if t0 = t then (TVar (Typing (env, e, t0))) else raise Hoge else let _ = typing rest e t in TVar (Typing (env, e, t)) end
  | Cal (op, e1, e2) -> let d1 = typing env e1 TyInt in let d2 = typing env e2 TyInt in begin match op with
        P -> if t = TyInt then TPlus (Typing (env, e, TyInt), d1, d2) else raise Hoge
      | M -> if t = TyInt then TMinus (Typing (env, e, TyInt), d1, d2) else raise Hoge
      | T -> if t = TyInt then TTimes (Typing (env, e, TyInt), d1, d2) else raise Hoge
      | L -> if t = TyBool then TLt (Typing (env, e, TyBool), d1, d2) else raise Hoge end
  | If (e1, e2, e3) -> let d1 = typing env e1 TyBool in let d2 = typing env e2 t in let d3 = typing env e3 t in TIf (Typing (env, e, t), d1, d2, d3)
  | Let (x, e1, e2, t1) -> let d1 = typing env e1 t1 in let d2= typing ((x, t1) :: env) e2 t in TLet (Typing (env, e, t), d1, d2)
  | Fun (x, e1) -> begin match t with
    | TyFun (t1, t2) -> let d1 = typing ((x, t1) :: env) e1 t2 in TFun (Typing (env, e, t), d1)
    | _ -> raise Hoge end
  | App (e1, e2, t1) -> let d1 = typing env e1 (TyFun (t1, t)) in let d2 = typing env e2 t1 in TApp (Typing (env, e, t), d1, d2)
  | LetRec (x, y, e1, e2, t1, t2) -> let d1 = typing ((y, t1) :: (x, TyFun (t1, t2)) :: env) e1 t2 in
    let d2 = typing ((x, TyFun (t1, t2)) :: env) e2 t in TLetRec (Typing (env, e, t), d1, d2)
  | Nil -> TNil (Typing (env, e, t))
  | Cons (e1, e2) -> begin match t with
      TyList t1 -> let d1 = typing env e1 t1 in let d2 = typing env e2 t in TCons (Typing (env, e, t), d1, d2)
    | _ -> raise Hoge end
  | Match (e1, e2, x, y, e3, t1) -> let d1 = typing env e1 (TyList t1) in let d2 = typing env e2 t in
    let d3 = typing ((y, TyList t1) :: (x, t1) :: env) e3 t in TMatch (Typing (env, e, t), d1, d2, d3)
and deriv (Typing (env, e, t)) = typing env e t

let string_judgement = function Typing (env, e, v) -> string_env env ^ " |- " ^ string_exp e ^ " : " ^ string_type v

let rec string_deriv = function
    TInt j -> string_judgement j ^ " by T-Int {}"
  | TBool j -> string_judgement j ^ " by T-Bool {}"
  | TVar j -> string_judgement j ^ " by T-Var {}"
  | TIf (j, d0, d1, d2) -> string_judgement j ^ " by T-If {\n" ^ string_deriv d0 ^ ";\n"  ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | TPlus (j, d0, d1) -> string_judgement j ^ " by T-Plus {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TMinus (j, d0, d1) -> string_judgement j ^ " by T-Minus {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TTimes (j, d0, d1) -> string_judgement j ^ " by T-Times {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TLt (j, d0, d1) -> string_judgement j ^ " by T-Lt {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TLet (j, d0, d1) -> string_judgement j ^ " by T-Let {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TFun (j, d0) -> string_judgement j ^ " by T-Fun {\n" ^ string_deriv d0 ^ "\n}"
  | TApp (j, d0, d1) -> string_judgement j ^ " by T-App {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TLetRec (j, d0, d1) -> string_judgement j ^ " by T-LetRec {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TNil j -> string_judgement j ^ " by T-Nil {}"
  | TCons (j, d0, d1) -> string_judgement j ^ " by T-Cons {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TMatch (j, d0, d1, d2) -> string_judgement j ^ " by T-Match {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"

let print_deriv j = print_string (string_deriv (deriv j))
let j99 = Typing ([], LetRec ("fact", "n", If (Cal (L, X "n", I 2), I 1, Cal (T, X "n", App (X "fact", Cal (M, X "n", I 1), TyInt))),
  App (X "fact", I 3, TyInt), TyInt, TyInt), TyInt)
let j100 = Typing ([], LetRec ("sum", "f", Fun ("n", If (Cal (L, X "n", I 1), I 0, Cal (P, App (X "f", X "n", TyInt), App (App (X "sum", X "f", TyFun (TyInt, TyInt)), Cal (M, X "n", I 1), TyInt)))),
  App (App (X "sum", Fun ("x", Cal (T, X "x", X "x")), TyFun (TyInt, TyInt)), I 2, TyInt), TyFun (TyInt, TyInt), TyFun (TyInt, TyInt)), TyInt)
let j101 = Typing ([], Let ("l", Cons (Fun ("x", X "x"), Cons (Fun ("y", I 2), Cons (Fun ("z", Cal (P, X "z", I 3)), Nil))), I 2, TyList (TyFun (TyInt, TyInt))), TyInt)
let j102 = Typing ([], LetRec ("length", "l", Match (X "l", I 0, "x", "y", Cal (P, I 1, App (X "length", X "y", TyList TyInt)), TyInt),
X "length", TyList TyInt, TyInt), TyFun (TyList TyInt, TyInt))
let j103 = Typing ([], LetRec ("length", "l", Match (X "l", I 0, "x", "y", Cal (P, I 1, App (X "length", X "y", TyList (TyFun (TyInt, TyInt)))), TyFun (TyInt, TyInt)),
App (X "length", Cons (Fun ("x", X "x"), Cons (Fun ("y", Cal (P, X "y", I 3)), Nil)), TyList (TyFun (TyInt, TyInt))), TyList (TyFun (TyInt, TyInt)), TyInt), TyInt)
let j104 = Typing ([], LetRec ("append", "l1", Fun ("l2", Match (X "l1", X "l2", "x", "y", Cons (X "x", App (App (X "append", X "y", TyList TyInt), X "l2", TyList TyInt)), TyInt)),
X "append", TyList TyInt, TyFun (TyList TyInt, TyList TyInt)), TyFun (TyList TyInt, TyFun (TyList TyInt, TyList TyInt)))
let j105 = Typing ([], LetRec ("append", "l1", Fun ("l2", Match (X "l1", X "l2", "x", "y", Cons (X "x", App (App (X "append", X "y", TyList TyBool), X "l2", TyList TyBool)), TyBool)),
App (App (X "append", Cons (B true, Nil), TyList TyBool), Cons (B false, Nil), TyList TyBool), TyList TyBool, TyFun (TyList TyBool, TyList TyBool)), TyList TyBool)
let j106 = Typing ([], LetRec ("map", "f", Fun ("l", Match (X "l", Nil, "x", "y", Cons (App (X "f", X "x", TyInt), App (App (X "map", X "f", TyFun (TyInt, TyBool)), X "y", TyList TyInt)), TyInt)),
App (App (X "map", Fun ("x", Cal (L, X "x", I 3)), TyFun (TyInt, TyBool)), Cons (I 4, Cons (I 5, Cons (I 1, Nil))), TyList TyInt), TyFun (TyInt, TyBool), TyFun (TyList TyInt, TyList TyBool)), TyList TyBool)