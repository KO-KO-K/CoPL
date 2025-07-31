exception Hoge
exception Fuga

type op = P | M | T | L
type exp =
    I of int
  | B of bool
  | X of string
  | Cal of op * exp * exp (*二項演算*)
  | If of exp * exp * exp
  | Let of string * exp * exp
  | Fun of string * exp
  | App of exp * exp
  | LetRec of string * string * exp * exp
  | Nil
  | Cons of exp * exp
  | Match of exp * exp * string * string * exp

type env = (string * value) list
and value = VInt of int | VBool of bool | VFun of env * string * exp | VRec of env * string * string * exp | VNil | VCons of value * value
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
  | EVar of judgement
  | ELet of judgement * derivation * derivation
  | EFun of judgement
  | EApp of judgement * derivation * derivation * derivation
  | ELetRec of judgement * derivation
  | EAppRec of judgement * derivation * derivation * derivation
  | ENil of judgement
  | ECons of judgement * derivation * derivation
  | EMatchNil of judgement * derivation * derivation
  | EMatchCons of judgement * derivation * derivation
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
    | _ -> "(" ^ string_exp e1 ^ ")" end ^ " " ^ begin match e2 with
      I _ | B _ | X _ -> string_exp e2
    | _ -> "(" ^ string_exp e2 ^ ")" end
  | LetRec (x, y, e1, e2) -> "let rec " ^ x ^ " = fun " ^ y ^ " -> " ^ string_exp e1 ^ " in " ^ string_exp e2
  | Nil -> "[]"
  | Cons (e1, e2) -> begin match e1 with
      I _ | B _ | X _ -> string_exp e1
    | _ -> "(" ^ string_exp e1 ^ ")" end ^ " :: " ^ string_exp e2
  | Match (e1, e2, x, y, e3) -> "match " ^ string_exp e1 ^ " with [] -> " ^ string_exp e2 ^ " | " ^ x ^ " :: " ^ y ^ " -> " ^ string_exp e3

let rec string_env env = match env with
    [] -> ""
  | [(x, v)] -> x ^ " = " ^ string_value v
  | (x, v) :: rest -> string_env rest ^ ", " ^ x ^ " = " ^ string_value v
and string_value v = match v with
    VInt i -> string_of_int i
  | VBool b -> string_of_bool b
  | VFun (env, x, e) -> "(" ^ string_env env ^ ")[fun " ^ x ^ " -> " ^ string_exp e ^ "]"
  | VRec (env, x, y, e) -> "(" ^ string_env env ^ ")[rec " ^ x ^ " = fun " ^ y ^ " -> " ^ string_exp e ^ "]"
  | VNil -> "[]"
  | VCons (v1, v2) -> begin match v1 with
      VInt _ | VBool _ -> string_value v1
    | _ -> "(" ^ string_value v1 ^ ")" end ^ " :: " ^ string_value v2

let rec eval env e = match e with
    I i -> (EInt (Evalto (env, e, VInt i)), VInt i)
  | B b -> (EBool (Evalto (env, e, VBool b)), VBool b)
  | X x -> begin match env with
      [] -> raise Hoge
    | (x0, v0) :: rest -> if x = x0 then (EVar (Evalto (env, e, v0)), v0) else let (_, v) = eval rest e in (EVar (Evalto (env, e, v)), v) end
  | Cal (op, e1, e2) -> let (d1, v1) = eval env e1 in let (d2, v2) = eval env e2 in begin match v1, v2 with
      VInt i1, VInt i2 -> begin match op with
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
  | Nil -> (ENil (Evalto (env, e, VNil)), VNil)
  | Cons (e1, e2) -> let (d1, v1) = eval env e1 in let (d2, v2) = eval env e2 in (ECons (Evalto (env, e, VCons (v1, v2)), d1, d2), VCons (v1, v2))
  | Match (e1, e2, x, y, e3) -> let (d1, v1) = eval env e1 in begin match v1 with
    | VNil -> let (d2, v2) = eval env e2 in (EMatchNil (Evalto (env, e, v2), d1, d2), v2)
    | VCons (v1', v2') -> let (d3, v3) = eval ((y, v2') :: (x, v1') :: env) e3 in (EMatchCons (Evalto (env, e, v3), d1, d3), v3)
    | _ -> raise Hoge end
and deriv j = match j with
    Plus (i1, i2, i3) -> if i1 + i2 = i3 then BPlus (Plus (i1, i2, i3)) else raise Hoge
  | Minus (i1, i2, i3) -> if i1 - i2 = i3 then BMinus (Minus (i1, i2, i3)) else raise Hoge
  | Times (i1, i2, i3) -> if i1 * i2 = i3 then BTimes (Times (i1, i2, i3)) else raise Hoge
  | Less (i1, i2, b) -> if i1 < i2 = b then BLT (Less (i1, i2, b)) else raise Hoge
  | Evalto (env, e, v) -> let (d, v0) = eval env e in if v = v0 then d else (print_string (string_value v0 ^ ", " ^ string_value v); raise Fuga)

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
  | EVar j -> string_judgement j ^ " by E-Var {}"
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
  | ENil j -> string_judgement j ^ " by E-Nil {}"
  | ECons (j, d0, d1) -> string_judgement j ^ " by E-Cons {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | EMatchNil (j, d0, d1) -> string_judgement j ^ " by E-MatchNil {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | EMatchCons (j, d0, d1) -> string_judgement j ^ " by E-MatchCons {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"

let print_deriv j = print_string (string_deriv (deriv j))
let j70 = Evalto ([], Cons (Cal (P, I 1, I 2), Cons (Cal (P, I 3, I 4), Nil)), VCons (VInt 3, VCons (VInt 7, VNil)))
let j71 = Evalto ([], Let ("f", Fun ("x", Match (X "x", I 0, "a", "b", X "a")),
Cal (P, Cal (P, App (X "f", Cons (I 4, Nil)), App (X "f", Nil)), App (X "f", Cons (I 1, Cons (I 2, Cons (I 3, Nil)))))), VInt 5)
let j72 = Evalto ([], LetRec ("f", "x", If (Cal (L, X "x", I 1), Nil, Cons (X "x", App (X "f", Cal (M, X "x", I 1)))), App (X "f", I 3)),
VCons (VInt 3, VCons (VInt 2, VCons (VInt 1, VNil))))
let j73 = Evalto ([], LetRec ("length", "l", Match (X "l", I 0, "x", "y", Cal (P, I 1, App (X "length", X "y"))),
App (X "length", Cons (I 1, Cons (I 2, Cons (I 3, Nil))))), VInt 3)
let j74 = Evalto ([], LetRec ("length", "l", Match (X "l", I 0, "x", "y", Cal (P, I 1, App (X "length", X "y"))),
App (X "length", Cons (Cons (I 1, Cons (I 2, Nil)), Cons (Cons (I 3, Cons (I 4, Cons (I 5, Nil))), Nil)))), VInt 2)
let j75 = Evalto ([], LetRec ("append", "l1", Fun ("l2", Match (X "l1", X "l2", "x", "y", Cons (X "x", App (App (X "append", X "y"), X "l2")))),
App (App (X "append", Cons (I 1, Cons (I 2, Nil))), Cons (I 3, Cons (I 4, Cons (I 5, Nil))))),
VCons (VInt 1, VCons (VInt 2, VCons (VInt 3, VCons (VInt 4, VCons (VInt 5, VNil))))))
let j76 = Evalto ([], LetRec ("apply", "l", Fun ("x", Match (X "l", X "x", "f", "l", App (X "f", App (App (X "apply", X "l"), X "x")))),
App (App (X "apply", Cons (Fun ("x", Cal (T, X "x", X "x")), Cons (Fun ("y", Cal (P, X "y", I 3)), Nil))), I 4)), VInt 49)
let j77 = Evalto ([], LetRec ("apply", "l", Fun ("x", Match (X "l", X "x", "f", "l", App (App (X "apply", X "l"), App (X "f", X "x")))),
App (App (X "apply", Cons (Fun ("x", Cal (T, X "x", X "x")), Cons (Fun ("y", Cal (P, X "y", I 3)), Nil))), I 4)), VInt 19)