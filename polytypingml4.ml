exception Hoge
exception Fuga

type op = P | M | T | L
type typing = TyVar of int | TyInt | TyBool | TyFun of typing * typing | TyList of typing
type tyscheme = TyScheme of int list * typing
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
  | Match of exp * exp * string * string * exp * typing

type env = (string * tyscheme) list
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
  | TAbs of judgement * derivation
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
      I _ | B _ | X _ | App _ -> string_exp e1
    | _ -> "(" ^ string_exp e1 ^ ")" end ^ " " ^ string_cal op ^ " " ^ begin match e2 with
      I _ | B _ | X _ | App _ -> string_exp e2
    | _ -> "(" ^ string_exp e2 ^ ")" end
  | If (e1, e2, e3) -> "if " ^ string_exp e1 ^ " then " ^ string_exp e2 ^ " else " ^ string_exp e3
  | Let (x, e1, e2, _) -> "let " ^ x ^ " = " ^ string_exp e1 ^ " in " ^ string_exp e2
  | Fun (x, e) -> "fun " ^ x ^ " -> " ^ string_exp e
  | App (e1, e2, _) -> begin match e1 with
      I _ | B _ | X _ | App _ -> string_exp e1
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
    TyVar i -> "'" ^ String.make 1 (char_of_int (97 + i))
  |  TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1, t2) -> begin match t1 with
    | TyFun _ -> "(" ^ string_type t1 ^ ")"
    | _ -> string_type t1 end ^ " -> " ^ string_type t2
  | TyList t0 -> begin match t0 with
    | TyFun _ -> "(" ^ string_type t0 ^ ")"
    | _ -> string_type t0 end ^ " list"

let rec string_tysc (TyScheme (tl, t)) = let tl0 = List.sort compare tl in match tl0 with
    [] -> string_type t
  | [i] -> string_type (TyVar i) ^ "." ^ string_type t
  | i :: rest -> string_type (TyVar i) ^ " " ^ string_tysc (TyScheme (rest, t))
let rec string_env (env : env) = match env with
    [] -> ""
  | [(x, t)] -> x ^ " : " ^ string_tysc t
  | (x, t) :: rest -> string_env rest ^ ", " ^ x ^ " : " ^ string_tysc t

let rec insert x = function
    [] -> [x]
  | y::rest -> if x = y then y :: rest else y :: insert x rest
let union xs ys =
  List.fold_left (fun zs x -> insert x zs) xs ys
let rec ftv t = match t with
    TyVar i -> [i]
  | TyInt | TyBool -> []
  | TyFun (t1, t2) -> union (ftv t1) (ftv t2)
  | TyList t -> ftv t

let rec ftv2 (e : env) = match e with
    [] -> []
  | (_ , TyScheme (_, t)) :: rest -> union (ftv t) (ftv2 rest)

let rec remove x = function
    [] -> []
  | y::rest -> if x = y then rest else y :: remove x rest
let diff xs ys =
  List.fold_left (fun zs x -> remove x zs) xs ys


let rec typing env e t = match e with
    I i -> TInt (Typing (env, e, TyInt))
  | B b -> TBool (Typing (env, e, TyBool))
  | X x -> begin match env with
      [] -> raise Hoge
    | (x0, TyScheme (tl, t0)) :: rest -> if x = x0 then (TVar (Typing (env, e, t))) else let _ = typing rest e t in TVar (Typing (env, e, t)) end
  | Cal (op, e1, e2) -> let d1 = typing env e1 TyInt in let d2 = typing env e2 TyInt in begin match op with
        P -> if t = TyInt then TPlus (Typing (env, e, TyInt), d1, d2) else raise Hoge
      | M -> if t = TyInt then TMinus (Typing (env, e, TyInt), d1, d2) else raise Hoge
      | T -> if t = TyInt then TTimes (Typing (env, e, TyInt), d1, d2) else raise Hoge
      | L -> if t = TyBool then TLt (Typing (env, e, TyBool), d1, d2) else raise Hoge end
  | If (e1, e2, e3) -> let d1 = typing env e1 TyBool in let d2 = typing env e2 t in let d3 = typing env e3 t in TIf (Typing (env, e, t), d1, d2, d3)
  | Let (x, e1, e2, t1) -> let d1 = typing env e1 t1 in let d2= typing ((x, TyScheme (diff (ftv t1) (ftv2 env), t1)) :: env) e2 t in TLet (Typing (env, e, t), d1, d2)
  | Fun (x, e1) -> begin match t with
    | TyFun (t1, t2) -> let d1 = typing ((x, TyScheme ([], t1)) :: env) e1 t2 in TAbs (Typing (env, e, t), d1)
    | _ -> raise Hoge end
  | App (e1, e2, t1) -> let d1 = typing env e1 (TyFun (t1, t)) in let d2 = typing env e2 t1 in TApp (Typing (env, e, t), d1, d2)
  | LetRec (x, y, e1, e2, t1, t2) -> let d1 = typing ((y, TyScheme ([], t1)) :: (x, TyScheme ([], TyFun (t1, t2))) :: env) e1 t2 in
    let d2 = typing ((x, TyScheme (diff (ftv (TyFun (t1, t2))) (ftv2 env), TyFun (t1, t2))) :: env) e2 t in TLetRec (Typing (env, e, t), d1, d2)
  | Nil -> TNil (Typing (env, e, t))
  | Cons (e1, e2) -> begin match t with
      TyList t1 -> let d1 = typing env e1 t1 in let d2 = typing env e2 t in TCons (Typing (env, e, t), d1, d2)
    | _ -> raise Hoge end
  | Match (e1, e2, x, y, e3, t1) -> let d1 = typing env e1 (TyList t1) in let d2 = typing env e2 t in
    let d3 = typing ((y, TyScheme ([], TyList t1)) :: (x, TyScheme ([], t1)) :: env) e3 t in TMatch (Typing (env, e, t), d1, d2, d3)
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
  | TAbs (j, d0) -> string_judgement j ^ " by T-Abs {\n" ^ string_deriv d0 ^ "\n}"
  | TApp (j, d0, d1) -> string_judgement j ^ " by T-App {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TLetRec (j, d0, d1) -> string_judgement j ^ " by T-LetRec {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TNil j -> string_judgement j ^ " by T-Nil {}"
  | TCons (j, d0, d1) -> string_judgement j ^ " by T-Cons {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | TMatch (j, d0, d1, d2) -> string_judgement j ^ " by T-Match {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"

let print_deriv j = print_string (string_deriv (deriv j))
let j107 = Typing ([], Fun ("x", X "x"), TyFun (TyVar 0, TyVar 0))
let j108 = Typing ([("f", TyScheme ([0], TyFun (TyVar 0, TyVar 0)))], App (X "f", I 3, TyInt), TyInt)
let j109 = Typing ([("f", TyScheme ([0], TyFun (TyVar 0, TyVar 0)))], App (X "f", Fun ("x", Cal (P, X "x", I 3)), TyFun (TyInt, TyInt)), TyFun (TyInt, TyInt))
let j110 = Typing ([], Let ("id", Fun ("x", X "x"), App (X "id", X "id", TyFun (TyBool, TyBool)), TyFun (TyVar 0, TyVar 0)), TyFun (TyBool, TyBool))
let j111 = Typing ([("f", TyScheme ([0; 1], TyFun (TyVar 0, TyFun (TyVar 1, TyVar 0))))],
Cal (P, App (App (X "f", I 3, TyInt), B true, TyBool), App (App (X "f", I 2, TyInt), I 4, TyInt)), TyInt)
let j112 = Typing ([], Let ("k", Fun ("x", Fun ("y", X "x")), Cons (App (App (X "k", I 3, TyInt), B true, TyBool), App (App (X "k", Cons (I 1, Nil), TyList TyInt), I 3, TyInt)), TyFun (TyVar 0, TyFun (TyVar 1, TyVar 0))), TyList TyInt)
let j113 = Typing ([], Let ("compose", Fun ("f", Fun ("g", Fun ("x", App (X "f", App (X "g", X "x", TyVar 2), TyVar 0)))),
  Let ("f", Fun ("x", If (X "x", I 3, I 4)), Let ("g", Fun ("x", Cal (L, X "x", I 4)),
  App (App (App (X "compose", X "f", TyFun (TyBool, TyInt)), App (App (X "compose", X "g", TyFun (TyInt, TyBool)), X "f", TyFun (TyBool, TyInt)), TyFun (TyBool, TyBool)), B true, TyBool),
  TyFun (TyInt, TyBool)), TyFun (TyBool, TyInt)), TyFun (TyFun (TyVar 0, TyVar 1), TyFun (TyFun (TyVar 2, TyVar 0), TyFun (TyVar 2, TyVar 1)))), TyInt)
let j114 = Typing ([], Let ("twice", Fun ("f", Fun ("x", App (X "f", App (X "f", X "x", TyVar 0), TyVar 0))),
  App (App (X "twice", Fun ("x", Cal (P, X "x", I 4)), TyFun (TyInt, TyInt)), I 5, TyInt), TyFun (TyFun (TyVar 0, TyVar 0), TyFun (TyVar 0, TyVar 0))), TyInt)
let j115 = Typing ([], Let ("twice", Fun ("f", Fun ("x", App (X "f", App (X "f", X "x", TyVar 0), TyVar 0))),
  App (App (App (X "twice", X "twice", TyFun (TyFun (TyInt, TyInt), TyFun (TyInt, TyInt))), Fun ("x", Cal (P, X "x", I 4)), TyFun (TyInt, TyInt)), I 5, TyInt), TyFun (TyFun (TyVar 0, TyVar 0), TyFun (TyVar 0, TyVar 0))), TyInt)
let j116 = Typing ([], Let ("s", Fun ("f", Fun ("g", Fun ("x", App (App (X "f", X "x", TyVar 0), App (X "g", X "x", TyVar 0), TyVar 1)))),
  Let ("k", Fun ("x", Fun ("y", X "x")), App (App (X "s", X "k", TyFun (TyVar 0, TyFun (TyFun (TyVar 1, TyVar 0), TyVar 0))), X "k", TyFun (TyVar 0, TyFun (TyVar 1, TyVar 0))),
  TyFun (TyVar 3, TyFun (TyVar 4, TyVar 3))), TyFun (TyFun (TyVar 0, TyFun (TyVar 1, TyVar 2)), TyFun (TyFun (TyVar 0, TyVar 1), TyFun (TyVar 0, TyVar 2)))), TyFun (TyVar 0, TyVar 0))
let j117 = Typing ([], Let ("x", Nil, Let ("y", Cons (I 3, X "x"), Cons (B true, X "x"), TyList TyInt), TyList (TyVar 0)), TyList TyBool)
let j118 = Typing ([], Let ("l", Cons(Fun ("x", X "x"), Nil), Let ("l1", Cons (Fun ("y", Cal (P, X "y", I 1)), X "l"),
Cons (Fun ("z", If (X "z", B false, B true)), X "l"), TyList (TyFun (TyInt, TyInt))), TyList (TyFun (TyVar 0, TyVar 0))), TyList (TyFun (TyBool, TyBool)))
let j119 = Typing ([], LetRec ("length", "l", Match (X "l", I 0, "x", "y", Cal (P, I 1, App (X "length", X "y", TyList (TyVar 0))), TyVar 0),
Cal (P, App (X "length", Cons (I 3, Cons (I 2, Nil)), TyList TyInt), App (X "length", Cons (Cons (I 1, Nil), Nil), TyList (TyList TyInt))), TyList (TyVar 0), TyInt), TyInt)
let j120 = Typing ([], LetRec ("map", "f", Fun ("l", Match (X "l", Nil, "x", "y", Cons (App (X "f", X "x", TyVar 0), App (App (X "map", X "f", TyFun (TyVar 0, TyVar 1)), X "y", TyList (TyVar 0))), TyVar 0)),
App (App (X "map", Fun ("x", Cal (L, X "x", I 3)), TyFun (TyInt, TyBool)), App (App (X "map", Fun ("x", Cal (T, X "x", I 2)), TyFun (TyInt, TyInt)), Cons (I 4, Cons (I 5, Cons (I 1, Nil))), TyList TyInt), TyList TyInt),
TyFun (TyVar 0, TyVar 1), TyFun (TyList (TyVar 0), TyList (TyVar 1))), TyList TyBool)
let j121 = Typing ([], LetRec ("map", "f", Fun ("l", Match (X "l", Nil, "x", "y", Cons (App (X "f", X "x", TyVar 0), App (App (X "map", X "f", TyFun (TyVar 0, TyVar 1)), X "y", TyList (TyVar 0))), TyVar 0)),
Let ("f", App (X "map", Fun ("x", X "x"), TyFun (TyVar 2, TyVar 2)), Let ("a", App (X "f", Cons (I 3, Nil), TyList TyInt), App (X "f", Cons (B true, Nil), TyList TyBool), TyList TyInt), TyFun (TyList (TyVar 2), TyList (TyVar 2))),
TyFun (TyVar 0, TyVar 1), TyFun (TyList (TyVar 0), TyList (TyVar 1))), TyList TyBool)
let j122 = Typing ([], Let ("f", Fun ("x", Let ("g", Fun ("y", Cons (X "x", Nil)), If (B true, App (X "g", I 3, TyInt), App (X "g", B false, TyBool)), TyFun (TyVar 1,  TyList (TyVar 0)))),
Match (App (X "f", I 2, TyInt), App (X "f", B true, TyBool), "x", "y", Nil, TyInt), TyFun (TyVar 0, TyList (TyVar 0))), TyList TyBool)
let j123 = Typing ([], Let ("f", Fun ("x", Let ("g", Fun ("y", Cons (App (X "y", X "x", TyVar 0), Nil)), App (X "g", Fun ("z", I 4), TyFun (TyVar 0, TyInt)), TyFun (TyFun (TyVar 0, TyVar 1),  TyList (TyVar 1)))),
Match (App (X "f", B true, TyBool), Cons (I 3, Nil), "x", "y", App (X "f", X "x", TyInt), TyInt), TyFun (TyVar 0, TyList TyInt)), TyList TyInt)