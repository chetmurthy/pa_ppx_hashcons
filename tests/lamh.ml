
(* programme de test de réductions massives de lambda-termes *)
(* version AVEC hash-consing *)
open Test_hashcons.LAM
open Hashcons

let ref x = term (Ref x)
let abs x = term (Abs x)
let app (x,y) = term (App(x,y))

module HT1_memo2_int_term = Ephemeron.K1.Make(struct
    type t = term
    let equal x y = x.tag = y.tag
    let hash = hash_term
  end)

module HT2_memo2_int_term = Hashtbl.Make(struct
    type t = int
    let equal x y = x = y
    let hash x = x
  end)

let ht1 = HT1_memo2_int_term.create 251
let memo2_int_term f (x : int) (y : term) =
  let v1 =
    try
      HT1_memo2_int_term.find ht1 y
    with Not_found -> begin
        let v1 = HT2_memo2_int_term.create 23 in
        HT1_memo2_int_term.add ht1 y v1 ;
        v1
      end in
  let v2 =
    try
      HT2_memo2_int_term.find v1 x
    with Not_found -> begin
        let v2 = f x y in
        HT2_memo2_int_term.add v1 x v2 ;
        v2
      end in
  v2
;;

module HT1_memo2_term_term = Ephemeron.K2.Make(struct
    type t = term
    let equal x y = x.tag = y.tag
    let hash = hash_term
  end)
    (struct
    type t = term
    let equal x y = x.tag = y.tag
    let hash = hash_term
  end)

let ht1 = HT1_memo2_term_term.create 251
let memo2_term_term f x y =
  try HT1_memo2_term_term.find ht1 (x,y)
  with Not_found ->
    let newval = f x y in
    HT1_memo2_term_term.add ht1 (x,y) newval;
 newval

let lift n = 
  let rec lift_rec k = 
    let rec lift_k t = match t.node with
    | Ref i -> 
	if i<k then (*Ref(i)*)t (* bound variables are invariant *)
	else ref(n+i)    (* free variables are relocated by n *)
    | Abs t   -> abs (lift_rec (k+1) t)
    | App (t, u) -> app (lift_k t, lift_k u)
    in
    lift_k
  in
  lift_rec 0 

let lift = memo2_int_term lift

let subst_count = Pervasives.ref 0

let subst w = 
  incr subst_count;
  let rec subst_w n t = match t.node with
    | Ref k -> 
	if k=n then lift n w      (* substituted variable *)
	else if k<n then (*Ref k*)t    (* bound variables *)
        else ref (k-1)       (* free variables *)
    | Abs t   -> abs (subst_w (n+1) t)
    | App (t, u) -> app (subst_w n t, subst_w n u)
  in 
  subst_w 0

let subst = memo2_term_term subst

let rec hnf t = match t.node with
  | Ref n -> t
  | Abs t   -> abs (hnf t)
  | App (t, u) -> match hnf t with
      | {node=Abs w} -> hnf (subst u w)
      | h     -> app (h, u)

let nhf = memo hnf

let rec nf t = match t.node with
  | Ref n -> t
  | Abs t   -> abs (nf t)
  | App (t, u) -> match hnf t with
      | {node=Abs w}  -> nf (subst u w)
      | h      -> app (nf h, nf u)

let nf = memo nf

type expr = Ref2 of int | Abs2 of expr | App2 of expr * expr
let rec term_of_expr = function
  | Ref2 i -> ref i
  | Abs2 t -> abs (term_of_expr t)
  | App2 (u,v) -> app (term_of_expr u, term_of_expr v)
let quicksort = 
  let c = open_in "quicksort.term" in
  let e = (input_value c : expr) in
  close_in c; 
  term_of_expr e

let nil = (*[c,n]n*) abs (abs (ref 0))
let cons = (*[x,l][c,n](c x (l c n))*)
  abs(abs(abs(abs(app(app (ref 1, 
			   ref 3),
		      app (app (ref 2, 
				ref 1), 
			   ref 0))))))

let zero = (*[s,z]z*) abs (abs (ref 0))
let succ = (*[n][s,z](s (n s z))*)
  abs(abs(abs(app (ref 1,
		   app (app (ref 2, ref 1), ref 0)))))

let rec iter f n x = if n=0 then x else iter f (n-1) (f x)

(* Church *)
let church n = iter (fun c -> nf (app (succ, c))) n zero

(* list : int list -> term *)
let rec list = function
  | x :: l -> 
      let cx = church x and ll = list l in 
      (*[c,n](c ^Cx (^Ll c n))*) 
      abs(abs(app (app (ref 1, cx),
		   app (app (ll, ref 1), ref 0))))
  | []   -> nil


(* and back *)

let eval_nat iter init = function
  | {node=Abs {node=Abs t}} (* [s,z]t *) -> 
      let rec eval_rec = function
        | (* z *) {node=Ref 0} -> init
        | (* (s u) *) {node=App ({node=Ref 1}, u)} -> iter (eval_rec u)
        | _ -> failwith "Not a normal church natural"
        in
	eval_rec t
  | _ -> failwith "Not a normal church natural"

let compute_nat = eval_nat (fun n->n+1) 0
 
let normal_nat n = compute_nat (nf n)

let eval_list_of_nats = function
  | {node=Abs {node=Abs t}} (* [c,n]t *) -> 
      let rec lrec = function
        | (* n *)       {node=Ref 0}                   -> []
        | (* (c x l) *) {node=App ({node=App ({node=Ref 1}, x)}, l)} -> 
	    (compute_nat x) :: (lrec l)
        | _ -> failwith "Not a normal List"
      in
      lrec t
  | _ -> failwith "Not a noraml List"


let normal_list l = eval_list_of_nats (nf l)

(* bench *)

open Format

(*let () = Gc.set { (Gc.get()) with Gc.verbose = 0x00d }*)

let () =
  let l = list [0;3;5;2;4;1] in 
  assert (normal_list (app (quicksort, l)) = [0;1;2;3;4;5]);
  printf "subst count: %d@." !subst_count;
  let stat = Gc.stat () in
  printf "top heap words: %d (%d kb)@." stat.Gc.top_heap_words
    (stat.Gc.top_heap_words / 256);
  let l,n,s,b1,b2,b3 = Term.stats term_ht in
  printf "table length: %d / nb. entries: %d / sum of bucket length: %d@."
    l n s;
  printf "smallest bucket: %d / median bucket: %d / biggest bucket: %d@."
    b1 b2 b3



