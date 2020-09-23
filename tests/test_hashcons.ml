(* camlp5o *)
(* test_hashcons.ml *)

type term =
    Ref of int
  | Abs of term
  | App of term * term[@@hashcons_module Term][@@hashcons_constructor term]
[@@deriving hashcons { module_name = LAM
                     ; memo = {
                         memo = [%typ: term]
                       ; memo2_term_int = [%typ: term * int]
                       ; memo2_int_term = [%typ: int * term]
                       ; memo2_term_term = [%typ: term * term]
                       }
                     }]
;;

type variable = int (* 1..max_var *) ;;
let preeq_variable x y = x = y ;;
let prehash_variable x = Hashtbl.hash x ;;

type bdd = Zero | One | Node of variable * bdd (*low*) * bdd (*high*)
[@@deriving hashcons { module_name = BDD
                     ; memo = {
                         memo_bdd = [%typ: bdd]
                       ; memo_bdd_bdd = [%typ: bdd * bdd]
                       }
                     }]
;;
