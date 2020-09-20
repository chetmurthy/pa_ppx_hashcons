(* camlp5o *)
(* test_hashcons.ml *)

type lam =
    V of int
  | Lam of lam
  | App of lam * lam
[@@deriving hashcons { module_name = LAM }]
;;
