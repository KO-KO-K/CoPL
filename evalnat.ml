exception Hoge
exception Fuga

type nat =
    Z
  | S of nat

type exp =
    N of nat
  | Sum of exp * exp
  | Prod of exp * exp

type judgement =
    Plus of nat * nat * nat
  | Times of nat * nat * nat
  | Evalto of exp * nat

type derivation =
    PZero of judgement
  | PSucc of judgement * derivation
  | TZero of judgement
  | TSucc of judgement * derivation * derivation
  | EConst of judgement
  | EPlus of judgement * derivation * derivation * derivation
  | ETimes of judgement * derivation * derivation * derivation

let rec plus n1 n2 = match n1 with
    Z -> n2
  | S n1' -> plus n1' (S n2)

let rec minus n1 n2 = match n2 with
    Z -> n1
  | S n2' -> match n1 with
      Z -> raise Hoge
    | S n1' -> minus n1' n2'

let rec times n1 n2 = match n2 with
    Z -> Z
  | S n2' -> plus n1 (times n1 n2')

let rec string_nat n = match n with
  | Z -> "Z"
  | S n' -> "S(" ^ string_nat n' ^ ")"

let rec eval e = match e with
    N n -> (EConst (Evalto (e, n)), n)
  | Sum (e1, e2) -> let (d1, n1) = eval e1 in let (d2, n2) = eval e2 in let n = plus n1 n2 in
    (EPlus (Evalto (e, n), d1, d2, deriv (Plus (n1, n2, n))), n)
  | Prod (e1, e2) -> let (d1, n1) = eval e1 in let (d2, n2) = eval e2 in let n = times n1 n2 in
    (ETimes (Evalto (e, n), d1, d2, deriv (Times (n1, n2, n))), n)
and deriv j = match j with
    Plus (Z, n2, n3) -> PZero (j)
  | Plus (S n1', n2, S n3') -> let d0 = Plus (n1', n2, n3') in PSucc (j, deriv d0)
  | Times (Z, n, Z) -> TZero (j)
  | Times (S n1', n2, n3) -> let n3' = minus n3 n2 in let d0 = Times (n1', n2, n3') in let d1 = Plus (n2, n3', n3) in TSucc (j, deriv d0, deriv d1)
  | Evalto (e, n) -> let (d, n0) = eval e in if n = n0 then d else (print_string (string_nat n ^ " " ^ string_nat n0); raise Fuga)
  | _ -> raise Hoge

let rec string_exp e = match e with
    N n -> string_nat n
  | Sum (e1, e2) -> string_exp e1 ^ " + (" ^ string_exp e2 ^ ")"
  | Prod (e1, e2) -> "(" ^ string_exp e1 ^ ") * (" ^ string_exp e2 ^ ")"

let string_judgement = function
    Plus (n1, n2, n3) -> string_nat n1 ^ " plus " ^ string_nat n2 ^ " is " ^ string_nat n3
  | Times (n1, n2, n3) -> string_nat n1 ^ " times " ^ string_nat n2 ^ " is " ^ string_nat n3
  | Evalto (e, n) -> string_exp e ^ " evalto " ^ string_nat n

let rec string_deriv = function
    PZero j -> string_judgement j ^ " by P-Zero {}"
  | PSucc (j, d) -> string_judgement j ^ " by P-Succ {\n" ^ string_deriv d ^ "\n}"
  | TZero j -> string_judgement j ^ " by T-Zero {}"
  | TSucc (j, d0, d1) -> string_judgement j ^ " by T-Succ {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | EConst j -> string_judgement j ^ " by E-Const {}"
  | EPlus (j, d0, d1, d2) -> string_judgement j ^ " by E-Plus {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"
  | ETimes (j, d0, d1, d2) -> string_judgement j ^ " by E-Times {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ ";\n" ^ string_deriv d2 ^ "\n}"

let print_deriv d = print_string(string_deriv (deriv d))