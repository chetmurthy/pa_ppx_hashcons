(* camlp5o *)
(* test_hashcons.ml *)

type term =
    Ref of int
  | Abs of term
  | App of term * term[@@hashcons_module Term][@@hashcons_constructor term]
[@@deriving hashcons { module_name = LAM
                     ; memo = {
                         memo_term = [%typ: term]
                       ; memo_int = [%typ: int]
                       ; memo_int2 = [%typ: int * int]
                       ; memo_int_int_int_int = [%typ: int * int * int * int]
                       ; memo_term_int = [%typ: term * int]
                       ; memo_int_term = [%typ: int * term]
                       ; memo_term_term = [%typ: term * term]
                       ; memo_term2_term = [%typ: (term * term) * term]
                       ; memo_term_term_term = [%typ: term * term * term]
                       ; memo_term2_term2 = [%typ: (term * term) * term * term]
                       ; memo_term4 = [%typ: term * term * term * term]
                       ; memo_term4_int2 = [%typ: term * int * term * term * int * term]
                       ; memo_term3_term = [%typ: ((term * term) * term) * term]
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
