(* camlp5o *)
(* test_hashcons.ml *)

type lam =
    V of int
  | Lam of lam
  | App of lam * lam[@@hashcons_module HCLam][@@hashcons_constructor lam]
[@@deriving hashcons { module_name = LAM
                     ; memo = {
                         memo = [%typ: lam]
                       ; memo_int_term = [%typ: int * lam]
                       ; memo_term_term = [%typ: term * lam]
                       }
                     }]
;;

type variable = int (* 1..max_var *) ;;
let preeq_variable x y = x = y ;;
let prehash_variable x = Hashtbl.hash x ;;

type bdd = Zero | One | Node of variable * bdd (*low*) * bdd (*high*)
[@@deriving hashcons { module_name = BDD }]
;;
