(* camlp5o *)
(* test_hashcons.ml *)

type lam =
    V of int
  | Lam of lam
  | App of lam * lam
[@@deriving hashcons { module_name = LAM }]
;;

type variable = int (* 1..max_var *) ;;
let preeq_variable x y = x = y ;

type bdd = Zero | One | Node of variable * bdd (*low*) * bdd (*high*)
[@@deriving hashcons { module_name = BDD }]
;;
