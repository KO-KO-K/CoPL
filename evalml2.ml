exception Hoge
exception Fuga

type op = P | M | T | L
type value = VInt of int | VBool of bool
type exp =
    I of int
  | B of bool
  | X of string
  | Cal of op * exp * exp
  | If of exp * exp * exp
  | Let of string * exp * exp

type env = (string * value) list (*逆順*)
type judgement =
    Plus of int * int * int
  | Minus of int * int * int
  | Times of int * int * int
  | Less of int * int * bool
  | Evalto of env * exp * value

type derivation =
  | BPlus of judgement
  | BMinus of judgement
  | BTimes of judgement
  | BLT of judgement
  | EInt of judgement
  | EBool of judgement
  | EVar1 of judgement
  | EVar2 of judgement * derivation
  | EIfT of judgement * derivation * derivation
  | EIfF of judgement * derivation * derivation
  | EPlus of judgement * derivation * derivation * derivation
  | EMinus of judgement * derivation * derivation * derivation
  | ETimes of judgement * derivation * derivation * derivation
  | ELT of judgement * derivation * derivation * derivation
  | ELet of judgement * derivation * derivation

let string_cal op = match op with
    P -> "+"
  | M -> "-"
  | T -> "*"
  | L -> "<"

let string_value v = match v with
    VInt i -> string_of_int i
  | VBool b -> string_of_bool b

let rec eval env e = match e with
    I i -> (EInt (Evalto (env, e, VInt i)), VInt i)
  | B b -> (EBool (Evalto (env, e, VBool b)), VBool b)
  | X x -> begin match env with
    [] -> raise Hoge
  | (x0, v0) :: rest -> if x = x0 then (EVar1 (Evalto (env, e, v0)), v0)
    else let (d1, v1) = eval rest e in (EVar2 (Evalto (env, e, v1), d1), v1) end
  | Cal (op, e1, e2) -> let (d1, v1) = eval env e1 in let (d2, v2) = eval env e2 in begin match v1, v2 with
  | VInt i1, VInt i2 -> begin match op with
        P -> let i = VInt (i1 + i2) in (EPlus (Evalto (env, e, i), d1, d2, deriv (Plus (i1, i2, i1 + i2))), i)
      | M -> let i = VInt (i1 - i2) in (EMinus (Evalto (env, e, i), d1, d2, deriv (Minus (i1, i2, i1 - i2))), i)
      | T -> let i = VInt (i1 * i2) in (ETimes (Evalto (env, e, i), d1, d2, deriv (Times (i1, i2, i1 * i2))), i)
      | L -> let b = VBool (i1 < i2) in (ELT (Evalto (env, e, b), d1, d2, deriv (Less (i1, i2, i1 < i2))), b) end
    | _ -> raise Hoge end
  | If (e1, e2, e3) -> let (d1, v1) = eval env e1 in begin match v1 with
    | VBool true -> let (d2, v2) = eval env e2 in (EIfT (Evalto (env, e, v2), d1, d2), v2)
    | VBool false -> let (d3, v3) = eval env e3 in (EIfF (Evalto (env, e, v3), d1, d3), v3)
    | _ -> raise Hoge end
  | Let (x, e1, e2) -> let (d1, v1) = eval env e1 in let (d2, v2) = eval ((x, v1) :: env) e2 in (ELet (Evalto (env, e, v2), d1, d2), v2)
and deriv j = match j with
    Plus (i1, i2, i3) -> if i1 + i2 = i3 then BPlus (Plus (i1, i2, i3)) else raise Hoge
  | Minus (i1, i2, i3) -> if i1 - i2 = i3 then BMinus (Minus (i1, i2, i3)) else raise Hoge
  | Times (i1, i2, i3) -> if i1 * i2 = i3 then BTimes (Times (i1, i2, i3)) else raise Hoge
  | Less (i1, i2, b) -> if i1 < i2 = b then BLT (Less (i1, i2, b)) else raise Hoge
  | Evalto (env, e, i) -> let (d, i0) = eval env e in if i = i0 then d else raise Fuga

let rec string_env env = match env with
    [] -> ""
  | [(x, v)] -> x ^ " = " ^ string_value v
  | (x, v) :: rest -> string_env rest ^ ", " ^ x ^ " = " ^ string_value v
let rec string_exp e = match e with
    I i -> string_of_int i
  | B b -> string_of_bool b
  | X x -> x
  | Cal (op, e1, e2) -> "(" ^ string_exp e1 ^ ") " ^ string_cal op ^ " (" ^ string_exp e2 ^ ")"
  | If (e1, e2, e3) -> "if (" ^ string_exp e1 ^ ") then (" ^ string_exp e2 ^ ") else (" ^ string_exp e3 ^ ")"
  | Let (s, e1, e2) -> "let " ^ s ^ " = " ^ string_exp e1 ^ " in " ^ string_exp e2

let string_judgement = function
    Plus (i1, i2, i3) -> string_of_int i1 ^ " plus " ^ string_of_int i2 ^ " is " ^ string_of_int i3
  | Minus (i1, i2, i3) -> string_of_int i1 ^ " minus " ^ string_of_int i2 ^ " is " ^ string_of_int i3
  | Times (i1, i2, i3) -> string_of_int i1 ^ " times " ^ string_of_int i2 ^ " is " ^ string_of_int i3
  | Less (i1, i2, b3) -> string_of_int i1 ^ " less than " ^ string_of_int i2 ^ " is " ^ string_of_bool b3
  | Evalto (env, e, v) -> string_env env ^ " |- " ^ string_exp e ^ " evalto " ^ string_value v

let rec string_deriv = function
    BPlus j -> string_judgement j ^ " by B-Plus {}"
  | BMinus j -> string_judgement j ^ " by B-Minus {}"
  | BTimes j -> string_judgement j ^ " by B-Times {}"
  | BLT j -> string_judgement j ^ " by B-Lt {}"
  | EInt j -> string_judgement j ^ " by E-Int {}"
  | EBool j -> string_judgement j ^ " by E-Bool {}"
  | EVar1 j -> string_judgement j ^ " by E-Var1 {}"
  | EVar2 (j, d0) -> string_judgement j ^ " by E-Var2 {\n" ^ string_deriv d0 ^ ";\n}"
  | EIfT (j, d0, d1) -> string_judgement j ^ " by E-IfT {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n}"
  | EIfF (j, d0, d1) -> string_judgement j ^ " by E-IfF {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n}"
  | EPlus (j, d0, d1, d2) -> string_judgement j ^ " by E-Plus {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | EMinus (j, d0, d1, d2) -> string_judgement j ^ " by E-Minus {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | ETimes (j, d0, d1, d2) -> string_judgement j ^ " by E-Times {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | ELT (j, d0, d1, d2) -> string_judgement j ^ " by E-Lt {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | ELet (j, d0, d1) -> string_judgement j ^ " by E-Let {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"

let print_deriv d = print_string(string_deriv (deriv d))
let j34 = Evalto ([("y", VInt 2); ("x", VInt 3)] , X "x", VInt 3)
let j35 = Evalto ([("y", VInt 4); ("x", VBool true)] , If (X "x", Cal (P, X "y", I 1), Cal (M, X "y", I 1)), VInt 5)
let j36 = Evalto ([], Let ("x", Cal (P, I 1, I 2), Cal (T, X "x", I 4)), VInt 12)
let j37 = Evalto ([], Let ("x", Cal (T, I 3, I 3), Let ("y", Cal (T, I 4, X "x"), Cal (P, X "x", X "y"))), VInt 45)
let j38 = Evalto ([("x", VInt 3)], Let ("x", Cal (T, X "x", I 2), Cal (P, X "x", X "x")), VInt 12)
let j39 = Evalto ([], Let ("x", Let ("y", Cal (M, I 3, I 2), Cal (T, X "y", X "y")), Let ("y", I 4, Cal (P, X "x", X "y"))), VInt 5)