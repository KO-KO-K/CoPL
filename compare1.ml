exception Hoge

type nat =
    Z
  | S of nat

type judgement =
    Plus of nat * nat * nat
  | Times of nat * nat * nat
  | Less of nat * nat

type derivation =
    PZero of judgement
  | PSucc of judgement * derivation
  | TZero of judgement
  | TSucc of judgement * derivation * derivation
  | LSucc of judgement
  | LTrans of judgement * derivation * derivation

let rec minus n1 n2 = match n2 with
    Z -> n1
  | S n2' -> match n1 with
      Z -> raise Hoge
    | S n1' -> minus n1' n2'

let rec deriv j = match j with
    Plus (Z, n2, n3) -> PZero (j)
  | Plus (S n1', n2, S n3') -> let d0 = Plus (n1', n2, n3') in PSucc (j, deriv d0)
  | Times (Z, n, Z) -> TZero (j)
  | Times (S n1', n2, n3) -> let n3' = minus n3 n2 in let d0 = Times (n1', n2, n3') in let d1 = Plus (n2, n3', n3) in TSucc (j, deriv d0, deriv d1)
  | Less (n1, n2) -> begin match minus n2 n1 with
      Z -> raise Hoge
    | S Z -> LSucc j
    | S n -> LTrans (j, LSucc (Less (n1, S n1)), deriv (Less (S n1, n2))) end
  | _ -> raise Hoge

let rec string_nat n = match n with
  | Z -> "Z"
  | S n' -> "S(" ^ string_nat n' ^ ")"

let string_judgement = function
    Plus (n1, n2, n3) -> string_nat n1 ^ " plus " ^ string_nat n2 ^ " is " ^ string_nat n3
  | Times (n1, n2, n3) -> string_nat n1 ^ " times " ^ string_nat n2 ^ " is " ^ string_nat n3
  | Less (n1, n2) -> string_nat n1 ^ " is less than " ^ string_nat n2

let rec string_deriv = function
    PZero j -> string_judgement j ^ " by P-Zero {}"
  | PSucc (j, d) -> string_judgement j ^ " by P-Succ {\n" ^ string_deriv d ^ "\n}"
  | TZero j -> string_judgement j ^ " by T-Zero {}"
  | TSucc (j, d0, d1) -> string_judgement j ^ " by T-Succ {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"
  | LSucc j -> string_judgement j ^ " by L-Succ {}"
  | LTrans (j, d0, d1) -> string_judgement j ^ " by L-Trans {\n" ^ string_deriv d0 ^ ";\n" ^ string_deriv d1 ^ "\n}"