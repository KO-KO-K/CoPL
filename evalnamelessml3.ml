exception Hoge
exception Fuga

type op = P | M | T | L
type exp =
    I of int
  | B of bool
  | N of int
  | Cal of op * exp * exp
  | If of exp * exp * exp
  | Let of exp * exp
  | Fun of exp
  | App of exp * exp
  | LetRec of exp * exp

type env = value list
and value = VInt of int | VBool of bool | VFun of env * exp | VRec of env * exp
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
  | BPlus of judgement
  | BMinus of judgement
  | BTimes of judgement
  | BLT of judgement

let rec get n env = match env with
    [] -> raise Hoge
  | h :: t -> if n = 1 then h else get (n - 1) t

let string_cal op = match op with
    P -> "+"
  | M -> "-"
  | T -> "*"
  | L -> "<"

let rec string_exp e = match e with
    I i -> string_of_int i
  | B b -> string_of_bool b
  | N n -> "#" ^ string_of_int n
  | Cal (op, e1, e2) -> begin match e1 with
      I _ | B _ | N _ -> string_exp e1
    | _ -> "(" ^ string_exp e1 ^ ")" end ^ " " ^ string_cal op ^ " " ^ begin match e2 with
      I _ | B _ | N _ -> string_exp e2
    | _ -> "(" ^ string_exp e2 ^ ")" end
  | If (e1, e2, e3) -> "if " ^ string_exp e1 ^ " then " ^ string_exp e2 ^ " else " ^ string_exp e3
  | Let (e1, e2) -> "let . = " ^ string_exp e1 ^ " in " ^ string_exp e2
  | Fun e -> "fun . -> " ^ string_exp e
  | App (e1, e2) -> begin match e1 with
      I _ | B _ | N _ -> string_exp e1
    | _ -> "(" ^ string_exp e1 ^ ") " end ^ " " ^ begin match e2 with
      I _ | B _ | N _ -> string_exp e2
    | _ -> "(" ^ string_exp e2 ^ ") " end
  | LetRec (e1, e2) -> "let rec . = fun . -> " ^ string_exp e1 ^ " in " ^ string_exp e2

let rec string_env env = match env with
    [] -> ""
  | [v] -> string_value v
  | v :: rest -> string_env rest ^ ", " ^ string_value v
and string_value v = match v with
    VInt i -> string_of_int i
  | VBool b -> string_of_bool b
  | VFun (env, e) -> "(" ^ string_env env ^ ")[fun . -> " ^ string_exp e ^ "]"
  | VRec (env, e) -> "(" ^ string_env env ^ ")[rec . = fun . -> " ^ string_exp e ^ "]"

let rec eval env e = match e with
    I i -> (EInt (Evalto (env, e, VInt i)), VInt i)
  | B b -> (EBool (Evalto (env, e, VBool b)), VBool b)
  | N n -> let v = get n env in (EVar (Evalto (env, e, v)), v)
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
  | Let (e1, e2) -> let (d1, v1) = eval env e1 in let (d2, v2) = eval (v1 :: env) e2 in (ELet (Evalto (env, e, v2), d1, d2), v2)
  | Fun e1 -> (EFun (Evalto (env, e, VFun (env, e1))), VFun (env, e1))
  | App (e1, e2) -> let (d1, v1) = eval env e1 in let (d2, v2) = eval env e2 in begin match v1 with
    | VFun (env0, e0) -> let (d3, v3) = eval (v2 :: env0) e0 in (EApp (Evalto (env, e, v3), d1, d2, d3), v3)
    | VRec (env0, e0) -> let (d3, v3) = eval (v2 :: v1 :: env0) e0 in (EAppRec (Evalto (env, e, v3), d1, d2, d3), v3)
    | _ -> raise Hoge end
  | LetRec (e1, e2) -> let v = VRec (env, e1) in let (d1, v1) = eval (v :: env) e2 in (ELetRec (Evalto (env, e, v1), d1), v1)
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

(*let reduce_paren s = let n = String.length s in
let rec reduce_paren0 s s0 n k = if k = n - 3 then s0 ^ String.sub s k 3 else match s.[k] with
| '(' -> if s.[k + 2] = ')' then reduce_paren0 s (s0 ^ Char.escaped s.[k + 1]) n (k + 3)
else if s.[k + 3] = ')' then reduce_paren0 s (s0 ^ String.sub s (k + 1) 2) n (k + 4)
else reduce_paren0 s (s0 ^ Char.escaped s.[k]) n (k + 1)
| _ -> reduce_paren0 s (s0 ^ String.sub s k 1) n (k + 1) in reduce_paren0 s "" n 0*)

let print_deriv j = print_string (string_deriv (deriv j))
let j55 = Evalto ([VInt 4; VBool true], If (N 2, Cal (P, N 1, I 1), Cal (M, N 1, I 1)), VInt 5)
let j57 = Evalto ([], Let (Cal (T, I 3, I 3), Let (Cal (T, I 4, N 1), Cal (P, N 2, N 1))), VInt 45)
let j59 = Evalto ([VInt 3], Let (Cal (T, N 1, I 2), Cal (P, N 1, N 1)), VInt 12)
let j61 = Evalto ([], Let (Let (Cal (M, I 3, I 2), Cal (T, N 1, N 1)), Let (I 4, Cal (P, N 2, N 1))), VInt 5)
let j63 = Evalto ([], Let (I 2, Fun (Cal (P, N 1, N 2))), VFun ([VInt 2], Cal (P, N 1, N 2)))
let j65 = Evalto ([], Let (Fun (Cal (P, App (N 1, I 3), App (N 1, I 4))), App (N 1, Fun (Cal (T, N 1, N 1)))), VInt 25)
let j67 = Evalto ([], Let (I 3, Let (Fun (Cal (T, N 1, N 2)), Let (I 5, App (N 2, I 4)))), VInt 12)
let j69 = Evalto ([], LetRec (If (Cal (L, N 1, I 2), I 1, Cal (T, N 1, App (N 2, Cal (M, N 1, I 1)))), App (N 1, I 3)), VInt 6)