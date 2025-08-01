exception Hoge
exception Fuga

type op = P | M | T | L
type value = VInt of int | VBool of bool
type exp =
    I of int
  | B of bool
  | Cal of op * exp * exp (*二項演算*)
  | If of exp * exp * exp

type judgement =
    Plus of int * int * int
  | Minus of int * int * int
  | Times of int * int * int
  | Less of int * int * bool
  | Evalto of exp * value

type derivation =
  | BPlus of judgement
  | BMinus of judgement
  | BTimes of judgement
  | BLT of judgement
  | EInt of judgement
  | EBool of judgement
  | EIfT of judgement * derivation * derivation
  | EIfF of judgement * derivation * derivation
  | EPlus of judgement * derivation * derivation * derivation
  | EMinus of judgement * derivation * derivation * derivation
  | ETimes of judgement * derivation * derivation * derivation
  | ELT of judgement * derivation * derivation * derivation

let string_cal op = match op with
    P -> "+"
  | M -> "-"
  | T -> "*"
  | L -> "<"

let rec eval e = match e with
    I i -> (EInt (Evalto (e, VInt i)), VInt i)
  | B b -> (EBool (Evalto (e, VBool b)), VBool b)
  | Cal (op, e1, e2) -> let (d1, v1) = eval e1 in let (d2, v2) = eval e2 in begin match v1, v2 with
  | VInt i1, VInt i2 -> begin match op with
        P -> let i = VInt (i1 + i2) in (EPlus (Evalto (e, i), d1, d2, deriv (Plus (i1, i2, i1 + i2))), i)
      | M -> let i = VInt (i1 - i2) in (EMinus (Evalto (e, i), d1, d2, deriv (Minus (i1, i2, i1 - i2))), i)
      | T -> let i = VInt (i1 * i2) in (ETimes (Evalto (e, i), d1, d2, deriv (Times (i1, i2, i1 * i2))), i)
      | L -> let b = VBool (i1 < i2) in (ELT (Evalto (e, b), d1, d2, deriv (Less (i1, i2, i1 < i2))), b) end
    | _ -> raise Hoge end
  | If (e1, e2, e3) -> let (d1, v1) = eval e1 in begin match v1 with
    | VBool true -> let (d2, v2) = eval e2 in (EIfT (Evalto (e, v2), d1, d2), v2)
    | VBool false -> let (d3, v3) = eval e3 in (EIfF (Evalto (e, v3), d1, d3), v3)
    | _ -> raise Hoge end
and deriv j = match j with
    Plus (i1, i2, i3) -> if i1 + i2 = i3 then BPlus (Plus (i1, i2, i3)) else raise Hoge
  | Minus (i1, i2, i3) -> if i1 - i2 = i3 then BMinus (Minus (i1, i2, i3)) else raise Hoge
  | Times (i1, i2, i3) -> if i1 * i2 = i3 then BTimes (Times (i1, i2, i3)) else raise Hoge
  | Less (i1, i2, b) -> if i1 < i2 = b then BLT (Less (i1, i2, b)) else raise Hoge
  | Evalto (e, i) -> let (d, i0) = eval e in if i = i0 then d else raise Fuga

let string_value v = match v with
    VInt i -> string_of_int i
  | VBool b -> string_of_bool b
let rec string_exp e = match e with
    I i -> string_of_int i
  | B b -> string_of_bool b
  | Cal (op, e1, e2) -> "(" ^ string_exp e1 ^ ") " ^ string_cal op ^ " (" ^ string_exp e2 ^ ")"
  | If (e1, e2, e3) -> "if (" ^ string_exp e1 ^ ") then (" ^ string_exp e2 ^ ") else (" ^ string_exp e3 ^ ")"

let string_judgement = function
    Plus (i1, i2, i3) -> string_of_int i1 ^ " plus " ^ string_of_int i2 ^ " is " ^ string_of_int i3
  | Minus (i1, i2, i3) -> string_of_int i1 ^ " minus " ^ string_of_int i2 ^ " is " ^ string_of_int i3
  | Times (i1, i2, i3) -> string_of_int i1 ^ " times " ^ string_of_int i2 ^ " is " ^ string_of_int i3
  | Less (i1, i2, b3) -> string_of_int i1 ^ " less than " ^ string_of_int i2 ^ " is " ^ string_of_bool b3
  | Evalto (e, v) -> string_exp e ^ " evalto " ^ string_value v

let rec string_deriv = function
    BPlus j -> string_judgement j ^ " by B-Plus {}"
  | BMinus j -> string_judgement j ^ " by B-Minus {}"
  | BTimes j -> string_judgement j ^ " by B-Times {}"
  | BLT j -> string_judgement j ^ " by B-Lt {}"
  | EInt j -> string_judgement j ^ " by E-Int {}"
  | EBool j -> string_judgement j ^ " by E-Bool {}"
  | EIfT (j, d0, d1) -> string_judgement j ^ " by E-IfT {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n}"
  | EIfF (j, d0, d1) -> string_judgement j ^ " by E-IfF {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n}"
  | EPlus (j, d0, d1, d2) -> string_judgement j ^ " by E-Plus {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | EMinus (j, d0, d1, d2) -> string_judgement j ^ " by E-Minus {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | ETimes (j, d0, d1, d2) -> string_judgement j ^ " by E-Times {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | ELT (j, d0, d1, d2) -> string_judgement j ^ " by E-Lt {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"

let print_deriv d = print_string(string_deriv (deriv d))
let time = Cal (T, Cal (P, I 4, I 5), Cal (M, I 1, I 10))
let k = Evalto (If (Cal (L, I 4, I 5), Cal (P, I 2, I 3), Cal (T, I 8, I 8)), VInt 5)
let j29 = Evalto (Cal (P, I 3, 
If (Cal (L, I (-23), Cal (T, I (-2), I 8)), I 8, Cal (P, I 2, I 4))), VInt 11)
let j30 = Evalto (Cal (P, (Cal (P, I 3, 
If (Cal (L, I (-23), Cal (T, I (-2), I 8)), I 8, I 2))), I 4), VInt 15)