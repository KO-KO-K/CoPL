exception Hoge
exception Fuga

type op = P | M | T | L
type exp =
    I of int
  | B of bool
  | X of string
  | Cal of op * exp * exp
  | If of exp * exp * exp
  | Let of string * exp * exp
  | Fun of string * exp
  | App of exp * exp
  | LetRec of string * string * exp * exp

type env = (string * value) list
and value = VInt of int | VBool of bool | VFun of env * string * exp | VRec of env * string * string * exp
type judgement =
    Plus of int * int * int
  | Minus of int * int * int
  | Times of int * int * int
  | Less of int * int * bool
  | Evalto of env * exp * value

type derivation =
  | EInt of judgement
  | EBool of judgement
  | EIfT of judgement * derivation * derivation
  | EIfF of judgement * derivation * derivation
  | EPlus of judgement * derivation * derivation * derivation
  | EMinus of judgement * derivation * derivation * derivation
  | ETimes of judgement * derivation * derivation * derivation
  | ELT of judgement * derivation * derivation * derivation
  | EVar1 of judgement
  | EVar2 of judgement * derivation
  | ELet of judgement * derivation * derivation
  | EFun of judgement
  | EApp of judgement * derivation * derivation * derivation
  | ELetRec of judgement * derivation
  | EAppRec of judgement * derivation * derivation * derivation
  | BPlus of judgement
  | BMinus of judgement
  | BTimes of judgement
  | BLT of judgement

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
  | Let (x, e1, e2) -> "let " ^ x ^ " = " ^ string_exp e1 ^ " in " ^ string_exp e2
  | Fun (x, e) -> "fun " ^ x ^ " -> " ^ string_exp e
  | App (e1, e2) -> begin match e1 with
      I _ | B _ | X _ -> string_exp e1
    | _ -> "(" ^ string_exp e1 ^ ") " end ^ " " ^ begin match e2 with
      I _ | B _ | X _ -> string_exp e2
    | _ -> "(" ^ string_exp e2 ^ ") " end
  | LetRec (x, y, e1, e2) -> "let rec " ^ x ^ " = fun " ^ y ^ " -> " ^ string_exp e1 ^ " in " ^ string_exp e2

let rec string_env env = match env with
    [] -> ""
  | [(x, v)] -> x ^ " = " ^ string_value v
  | (x, v) :: rest -> string_env rest ^ ", " ^ x ^ " = " ^ string_value v
and string_value v = match v with
    VInt i -> string_of_int i
  | VBool b -> string_of_bool b
  | VFun (env, x, e) -> "(" ^ string_env env ^ ")[fun " ^ x ^ " -> " ^ string_exp e ^ "]"
  | VRec (env, x, y, e) -> "(" ^ string_env env ^ ")[rec " ^ x ^ " = fun " ^ y ^ " -> " ^ string_exp e ^ "]"

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
  | Fun (x, e1) -> (EFun (Evalto (env, e, VFun (env, x, e1))), VFun (env, x, e1))
  | App (e1, e2) -> let (d1, v1) = eval env e1 in let (d2, v2) = eval env e2 in begin match v1 with
    | VFun (env0, x0, e0) -> let (d3, v3) = eval ((x0, v2) :: env0) e0 in (EApp (Evalto (env, e, v3), d1, d2, d3), v3)
    | VRec (env0, x0, y0, e0) -> let (d3, v3) = eval ((y0, v2) :: (x0, v1) :: env0) e0 in (EAppRec (Evalto (env, e, v3), d1, d2, d3), v3)
    | _ -> raise Hoge end
  | LetRec (x, y, e1, e2) -> let v = VRec (env, x, y, e1) in let (d1, v1) = eval ((x, v) :: env) e2 in (ELetRec (Evalto (env, e, v1), d1), v1)
and deriv j = match j with
    Plus (i1, i2, i3) -> if i1 + i2 = i3 then BPlus (Plus (i1, i2, i3)) else raise Hoge
  | Minus (i1, i2, i3) -> if i1 - i2 = i3 then BMinus (Minus (i1, i2, i3)) else raise Hoge
  | Times (i1, i2, i3) -> if i1 * i2 = i3 then BTimes (Times (i1, i2, i3)) else raise Hoge
  | Less (i1, i2, b) -> if i1 < i2 = b then BLT (Less (i1, i2, b)) else raise Hoge
  | Evalto (env, e, v) -> let (d, v0) = eval env e in if v = v0 then d else raise Fuga

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
  | EVar2 (j, d0) -> string_judgement j ^ " by E-Var2 {\n" ^ string_deriv d0 ^ "\n}"
  | EIfT (j, d0, d1) -> string_judgement j ^ " by E-IfT {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | EIfF (j, d0, d1) -> string_judgement j ^ " by E-IfF {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | EPlus (j, d0, d1, d2) -> string_judgement j ^ " by E-Plus {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | EMinus (j, d0, d1, d2) -> string_judgement j ^ " by E-Minus {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | ETimes (j, d0, d1, d2) -> string_judgement j ^ " by E-Times {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | ELT (j, d0, d1, d2) -> string_judgement j ^ " by E-Lt {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | ELet (j, d0, d1) -> string_judgement j ^ " by E-Let {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | EFun j -> string_judgement j ^ " by E-Fun {}"
  | EApp (j, d0, d1, d2) -> string_judgement j ^ " by E-App {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | ELetRec (j, d0) -> string_judgement j ^ " by E-LetRec {\n" ^ string_deriv d0 ^ "\n}"
  | EAppRec (j, d0, d1, d2) -> string_judgement j ^ " by E-AppRec {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"

(*let reduce_paren s = let n = String.length s in
let rec reduce_paren0 s s0 n k = if k = n - 3 then s0 ^ String.sub s k 3 else match s.[k] with
| '(' -> if s.[k + 2] = ')' then reduce_paren0 s (s0 ^ Char.escaped s.[k + 1]) n (k + 3)
else if s.[k + 3] = ')' then reduce_paren0 s (s0 ^ String.sub s (k + 1) 2) n (k + 4)
else reduce_paren0 s (s0 ^ Char.escaped s.[k]) n (k + 1)
| _ -> reduce_paren0 s (s0 ^ String.sub s k 1) n (k + 1) in reduce_paren0 s "" n 0*)

let print_deriv j = print_string (string_deriv (deriv j))
let j40 = Evalto ([], Fun ("x", Cal (P, X "x", I 1)), VFun ([], "x", Cal (P, X "x", I 1)))
let j41 = Evalto ([], Let ("y", I 2, Fun ("x", Cal (P, X "x", X "y"))), VFun ([("y", VInt 2)], "x", Cal (P, X "x", X "y")))
let j42 = Evalto ([], Let ("sq", Fun ("x", Cal (T, X "x", X "x")), Cal (P, App (X "sq", I 3), App (X "sq", I 4))), VInt 25)
let j43 = Evalto ([], Let ("sm", Fun ("f", Cal (P, App (X "f", I 3), App (X "f", I 4))), App (X "sm", Fun ("x", Cal (T, X "x", X "x")))), VInt 25)
let j44 = Evalto ([], Let ("max", Fun ("x", Fun ("y", If (Cal (L, X "x", X "y"), X "y", X "x"))), App (App (X "max", I 3), I 5)), VInt 5)
let j45 = Evalto ([], Let ("a", I 3, Let ("f", Fun ("y", Cal (T, X "y", X "a")), Let ("a", I 5, App (X "f", I 4)))), VInt 12)
let j46 = Evalto ([], Let ("twice", Fun ("f", Fun ("x", App (X "f", App (X "f", X "x")))),
  App (App (X "twice", Fun ("x", Cal (T, X "x", X "x"))), I 2)), VInt 16)
let j47 = Evalto ([], Let ("twice", Fun ("f", Fun ("x", App (X "f", App (X "f", X "x")))),
  App (App (App (X "twice", X "twice"), Fun ("x", Cal (T, X "x", X "x"))), I 2)), VInt 65536)
let j48 = Evalto ([], Let ("compose", Fun ("f", Fun ("g", Fun ("x", App (X "f", App (X "g", X "x"))))),
  Let ("p", Fun ("x", Cal (T, X "x", X "x")), Let ("q", Fun ("x", Cal (P, X "x", I 4)), App (App (App (X "compose", X "p"), X "q"), I 4)))), VInt 64)
let j49 = Evalto ([], Let ("s", Fun ("f", Fun ("g", Fun ("x", App (App (X "f", X "x"), App (X "g", X "x"))))),
  Let ("k", Fun ("x", Fun ("y", X "x")), App (App (App (X "s", X "k"), X "k"), I 7))), VInt 7)
let j50 = Evalto ([], LetRec ("fact", "n", If (Cal (L, X "n", I 2), I 1, Cal (T, X "n", App (X "fact", Cal (M, X "n", I 1)))),
  App (X "fact", I 3)), VInt 6)
let j51 = Evalto ([], LetRec ("fib", "n", If (Cal (L, X "n", I 3), I 1, Cal (P, App (X "fib", Cal (M, X "n", I 1)), App (X "fib", Cal (M, X "n", I 2)))),
  App (X "fib", I 5)), VInt 5)
let j52 = Evalto ([], LetRec ("sum", "f", Fun ("n", If (Cal (L, X "n", I 1), I 0, Cal (P, App (X "f", X "n"), App (App (X "sum", X "f"), Cal (M, X "n", I 1))))),
  App (App (X "sum", Fun ("x", Cal (T, X "x", X "x"))), I 2)), VInt 5)
let j53 = Evalto ([], Let ("fact", Fun ("self", Fun ("n", If (Cal (L, X "n", I 2), I 1, Cal (T, X "n", App (App (X "self", X "self"), Cal (M, X "n", I 1)))))),
  App (App (X "fact", X "fact"), I 3)), VInt 6)