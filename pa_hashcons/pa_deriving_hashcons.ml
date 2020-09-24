(* camlp5r *)
(* pa_deriving_migrate.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_macro_gram.cmo";
#load "pa_extfun.cmo";

open Asttools;
open MLast;
open Pa_ppx_base ;
open Pa_passthru ;
open Ppxutil ;
open Surveil ;
open Pa_deriving_base ;
open Pa_ppx_utils ;

value debug = Pa_passthru.debug ;

value canon_expr e = Reloc.expr (fun _ -> Ploc.dummy) 0 e ;
value canon_ctyp ty = Reloc.ctyp (fun _ -> Ploc.dummy) 0 ty ;
value builtin_types =
  let loc = Ploc.dummy in
  List.map canon_ctyp [
    <:ctyp< string >>
  ; <:ctyp< int >>
  ; <:ctyp< int32 >>
  ; <:ctyp< int64 >>
  ; <:ctyp< nativeint >>
  ; <:ctyp< float >>
  ; <:ctyp< bool >>
  ; <:ctyp< char >>
  ]
;

module HC = struct
type t = {
  module_name : string
; type_decls : list (string * MLast.type_decl)
; memo : list (string * choice (list (bool * MLast.ctyp)) (list (bool * MLast.ctyp)))
}
;

value extract_memo_type_list type_decls t =
  let rec rec_memo_type = fun [
    <:ctyp< $lid:lid$ >> when List.mem_assoc lid type_decls -> True
  | <:ctyp< ( $list:l$ ) >> -> List.for_all rec_memo_type l
  | _ -> False
  ] in
  let rec prim_type = fun [
    z when List.mem (canon_ctyp z) builtin_types -> True
  | <:ctyp< ( $list:l$ ) >> when List.for_all prim_type l -> True
  | _ -> False
  ] in
  let memoizable t = rec_memo_type t || prim_type t in
  match t with [
    z when prim_type z -> Left [(False, z)]
  | <:ctyp< $lid:_$ >> as z when rec_memo_type z -> Left [(True, z)]
  | <:ctyp< ( $t1$ * $t2$ ) >> when rec_memo_type t1 && rec_memo_type t2 -> Left [(True, t1);(True, t2)]

  | <:ctyp< ( $list:l$ ) >> when List.for_all memoizable l ->
    Right (List.map (fun z -> (rec_memo_type z, z)) l)

  | _ -> Ploc.raise (loc_of_ctyp t)
           (Failure Fmt.(str "extract_memo_type_list: not memoizable type:@ %a"
                           Pp_MLast.pp_ctyp t))
  ]
;

value build_context loc ctxt tdl =
  let type_decls = List.map (fun (MLast.{tdNam=tdNam} as td) ->
      (tdNam |> uv |> snd |> uv, td)
    ) tdl in
  let open Ctxt in
  let module_name = match option ctxt "module_name" with [
    <:expr< $uid:mname$ >> -> mname
  | _ -> Ploc.raise loc (Failure "pa_deriving_hashcons: option module_name must be a UIDENT")
  | exception Failure _ ->
  Ploc.raise loc (Failure "pa_deriving_hashcons: option module_name must be specified")
  ] in
  let memo = match option ctxt "memo" with [
    <:expr< { $list:lel$ } >> ->
    List.map (fun [
        (<:patt< $lid:memo_fname$ >>, <:expr< [%typ: $type:t$] >>) -> 
        (memo_fname, extract_memo_type_list type_decls t)
      | _ -> Ploc.raise loc (Failure "pa_deriving_hashcons: bad memo record-members")
      ]) lel
  | _ -> Ploc.raise loc (Failure "pa_deriving_hashcons: option memo requires a record argument")
  ] in
  {
    module_name = module_name
  ; type_decls = type_decls
  ; memo = memo
  }
;

value generate_eq_expression loc ctxt rc ty =
  let rec prerec = fun [
    <:ctyp:< $lid:lid$ >> as z when List.mem_assoc lid rc.type_decls ->
    <:expr< (fun (x : $z$)  (y : $z$) -> x == y) >>
  | <:ctyp:< ( $list:l$ ) >> ->
    let xpatt_ypatt_subeqs =
      List.mapi (fun i ty ->
          let x = Printf.sprintf "x_%d" i in
          let y = Printf.sprintf "y_%d" i in
          (<:patt< $lid:x$ >>,
           <:patt< $lid:y$ >>,
           <:expr< $prerec ty$ $lid:x$ $lid:y$ >>)) l in
    let xpatt (x, _, _) = x in
    let ypatt (_, x, _) = x in
    let subeq (_, _, x) = x in
    let rhs = List.fold_right (fun x e -> <:expr< $subeq x$ && $e$ >>) xpatt_ypatt_subeqs <:expr< True >> in
    <:expr< (fun ( $list:List.map xpatt xpatt_ypatt_subeqs$ )
            ( $list:List.map ypatt xpatt_ypatt_subeqs$ ) -> $rhs$) >>

  | <:ctyp:< { $list:ltl$ } >> ->
    let xlpatt_ylpatt_subeqs =
      List.mapi (fun i (_, id, _, ty, _) ->
          let x = Printf.sprintf "x_%d" i in
          let y = Printf.sprintf "y_%d" i in
          ((<:patt< $lid:id$ >>, <:patt< $lid:x$ >>),
           (<:patt< $lid:id$ >>, <:patt< $lid:y$ >>),
           <:expr< $prerec ty$ $lid:x$ $lid:y$ >>)) ltl in
    let xlpatt (x, _, _) = x in
    let ylpatt (_, x, _) = x in
    let subeq (_, _, x) = x in
    let rhs = List.fold_right (fun x e -> <:expr< $subeq x$ &&  $e$ >>) xlpatt_ylpatt_subeqs <:expr< True >> in
    <:expr< (fun { $list:List.map xlpatt xlpatt_ylpatt_subeqs$ }
            { $list:List.map ylpatt xlpatt_ylpatt_subeqs$ } -> $rhs$) >>

  | <:ctyp:< [ $list:l$ ] >> ->
    let case_branches =
      List.map (fun [
          <:constructor< $uid:ci$ of $list:tl$ >> ->
          let xpatt_ypatt_subeqs =
            List.mapi (fun i ty ->
                let x = Printf.sprintf "x_%d" i in
                let y = Printf.sprintf "y_%d" i in
                (<:patt< $lid:x$ >>,
                 <:patt< $lid:y$ >>,
                 <:expr< $prerec ty$ $lid:x$ $lid:y$ >>)) tl in
          let xpatt (x, _, _) = x in
          let ypatt (_, x, _) = x in
          let subeq (_, _, x) = x in
          let xconspat = Patt.applist <:patt< $uid:ci$ >> (List.map xpatt xpatt_ypatt_subeqs) in
          let yconspat = Patt.applist <:patt< $uid:ci$ >> (List.map ypatt xpatt_ypatt_subeqs) in
          let rhs = List.fold_right (fun x e -> <:expr< $subeq x$ && $e$ >>) xpatt_ypatt_subeqs <:expr< True >> in
          (<:patt< ($xconspat$, $yconspat$) >>, <:vala< None >>, rhs)
        ]) l in
    let case_branches = case_branches @ [
      (<:patt< _ >>, <:vala< None >>, <:expr< False >>)
    ] in
    <:expr< (fun x y -> match (x,y) with [ $list:case_branches$ ] ) >>

  | z when List.mem (canon_ctyp z) builtin_types ->
    <:expr< (fun (x : $z$) (y : $z$) -> x = y) >>

  | <:ctyp:< $lid:lid$ >> ->
    let eq_name = "preeq_"^lid in
    <:expr< $lid:eq_name$ >>

  | z -> Ploc.raise loc (Failure Fmt.(str "generate_pre_eq_binding: unhandled type %a"
                                        Pp_MLast.pp_ctyp z))

  ] in
  prerec ty
;

value generate_pre_eq_binding ctxt rc (name, td) =
  let loc = loc_of_type_decl td in
  let rhs = generate_eq_expression loc ctxt rc td.tdDef in
  let eq_fname = "preeq_"^name^"_node" in
  (<:patt< $lid:eq_fname$ >>, rhs, <:vala< [] >>)
;

value generate_hash_expression loc ctxt rc ty =
  let rec prerec = fun [
    <:ctyp:< $lid:lid$ >> when List.mem_assoc lid rc.type_decls ->
    <:expr< (fun x -> x.hkey) >>
  | <:ctyp:< ( $list:l$ ) >> ->
    let xpatt_subhashs =
      List.mapi (fun i ty ->
          let x = Printf.sprintf "x_%d" i in
          (<:patt< $lid:x$ >>,
           <:expr< $prerec ty$ $lid:x$ >>)) l in
    let xpatt (x, _) = x in
    let subhash (_, x) = x in
    let rhs = List.fold_right (fun x e -> <:expr< 19 * $subhash x$ + $e$ >>) xpatt_subhashs <:expr< 0 >> in
    <:expr< (fun ( $list:List.map xpatt xpatt_subhashs$ ) -> $rhs$) >>

  | <:ctyp:< { $list:ltl$ } >> ->
    let xlpatt_subhashs =
      List.mapi (fun i (_, id, _, ty, _) ->
          let x = Printf.sprintf "x_%d" i in
          ((<:patt< $lid:id$ >>, <:patt< $lid:x$ >>),
           <:expr< $prerec ty$ $lid:x$ >>)) ltl in
    let xlpatt (x, _) = x in
    let subhash (_, x) = x in
    let rhs = List.fold_right (fun x e -> <:expr< 19 * $subhash x$ + $e$ >>) xlpatt_subhashs <:expr< 0 >> in
    <:expr< (fun { $list:List.map xlpatt xlpatt_subhashs$ } -> $rhs$) >>

  | <:ctyp:< [ $list:l$ ] >> ->
    let case_branches =
      List.mapi (fun pos -> fun [
          <:constructor< $uid:ci$ of $list:tl$ >> ->
          let xpatt_subhashs =
            List.mapi (fun i ty ->
                let x = Printf.sprintf "x_%d" i in
                (<:patt< $lid:x$ >>,
                 <:expr< $prerec ty$ $lid:x$ >>)) tl in
          let xpatt (x, _) = x in
          let subhash (_, x) = x in
          let xconspat = Patt.applist <:patt< $uid:ci$ >> (List.map xpatt xpatt_subhashs) in
          let rhs = List.fold_right (fun x e -> <:expr< 19 * $subhash x$ + $e$ >>) xpatt_subhashs <:expr< $int:string_of_int pos$ >> in
          (<:patt< $xconspat$ >>, <:vala< None >>, rhs)
        ]) l in
    <:expr< fun [ $list:case_branches$ ] >>

  | z when List.mem (canon_ctyp z) builtin_types ->
    <:expr< (fun x -> Hashtbl.hash x) >>

  | <:ctyp:< $lid:lid$ >> ->
    let eq_name = "prehash_"^lid in
    <:expr< $lid:eq_name$ >>

  | z -> Ploc.raise loc (Failure Fmt.(str "generate_pre_hash_binding: unhandled type %a"
                                        Pp_MLast.pp_ctyp z))

  ] in
  prerec ty
;

value generate_pre_hash_binding ctxt rc (name, td) =
  let loc = loc_of_type_decl td in
  let rhs = generate_hash_expression loc ctxt rc td.tdDef in
  let hash_fname = "prehash_"^name^"_node" in
  (<:patt< $lid:hash_fname$ >>, rhs, <:vala< [] >>)
;

value generate_hash_bindings ctxt rc (name, td) =
  let loc = loc_of_type_decl td in
  let node_rhs = generate_hash_expression loc ctxt rc td.tdDef in
  let node_hash_fname = "hash_"^name^"_node" in

  let hc_rhs = <:expr< (fun (x : $lid:name$) -> x.hkey) >> in
  let hc_fname = "hash_"^name in
  [(<:patt< $lid:node_hash_fname$ >>, node_rhs, <:vala< [] >>)
  ; (<:patt< $lid:hc_fname$ >>, hc_rhs, <:vala< [] >>)]
;

value ctyp_make_tuple loc l =
  match l with [
    [] -> Ploc.raise loc (Failure "ctyp_make_tuple: invalid empty-list arg")
  | [t] -> t
  | l -> <:ctyp< ( $list:l$ ) >>
  ]
;

value expr_make_tuple loc l =
  match l with [
    [] -> Ploc.raise loc (Failure "expr_make_tuple: invalid empty-list arg")
  | [t] -> t
  | l -> <:expr< ( $list:l$ ) >>
  ]
;

value find_matching_memo loc rc l =
  let eq_lists l1 l2 =
    List.length l1 = List.length l2 &&
    List.for_all2 (fun (b1, t1) (b2, t2) ->
        b1=b2 && Reloc.eq_ctyp t1 t2) l1 l2 in
  match List.find_map (fun (memo, t) ->
    match t with [
      Right _ -> None
    | Left l' when eq_lists l l' -> Some memo
    | _ -> None
    ]) rc.memo with [
    Some n -> n
  | None ->
    let pp_ctyp = Pp_MLast.pp_ctyp in
    Ploc.raise loc (Failure Fmt.(str "find_matching_memo: no match:@ %s"
                                   ([%show: list (bool * ctyp)] l)))
  ]
;

value to_expr loc (v, (_, _)) = <:expr< $lid:v$ >> ;
value to_patt loc (v, (_, _)) = <:patt< $lid:v$ >> ;
value to_typatt loc (v, (_, ty)) = <:patt< ( $lid:v$ : $ty$ ) >> ;
value to_ctyp (_, (_, ty)) = ty ;

value generate_memo_item loc ctxt rc (memo_fname, memo_tys) =
  match memo_tys with [

    Left l when not (List.exists fst l) ->
    let vars_types = List.mapi (fun i x -> (Printf.sprintf "v_%d" i, x)) l in
    let vars_exps = List.map (to_expr loc) vars_types in
    let vars_patts = List.map (to_patt loc) vars_types in
    let z = ctyp_make_tuple loc (List.map to_ctyp vars_types) in
    let vars_tuple = expr_make_tuple loc vars_exps in
    let mname = Printf.sprintf "HT_%s" memo_fname in
    let recompute_expr = Expr.applist <:expr< f >> vars_exps in
    let body = <:expr<
          try $uid:mname$.find ht $vars_tuple$
          with [ Not_found -> do {
            let newv = $recompute_expr$ in 
            $uid:mname$.add ht $vars_tuple$ newv ;
            newv
          }]
      >> in
    let fun_body = Expr.abstract_over vars_patts body in
    <:str_item<
      declare
        module $mname$ = Hashtbl.Make(struct
          type t = $z$ ;
          value equal = $generate_eq_expression loc ctxt rc z$ ;
          value hash = $generate_hash_expression loc ctxt rc z$ ;
        end) ;
      value $lid:memo_fname$ f ht =
        $fun_body$
        ;
      end
     >>

  | Left [(True, z)] ->
    let mname = Printf.sprintf "HT_%s" memo_fname in
    <:str_item<
      declare
        module $mname$ = Ephemeron.K1.Make(struct
          type t = $z$ ;
          value equal = $generate_eq_expression loc ctxt rc z$ ;
          value hash = $generate_hash_expression loc ctxt rc z$ ;
        end) ;
      value $lid:memo_fname$ f =
        let ht = $uid:mname$.create 251 in
        fun ( x : $z$ ) ->
          try $uid:mname$.find ht x
          with [ Not_found -> do {
            let newv = f x in 
            $uid:mname$.add ht x newv ;
            newv
          }]
        ;
      end
     >>

  | Left [(True, z0); (True, z1)] ->
    let mname = Printf.sprintf "HT_%s" memo_fname in
    <:str_item<
      declare
        module $mname$ = Ephemeron.K2.Make
          (struct
            type t = $z0$ ;
            value equal = $generate_eq_expression loc ctxt rc z0$ ;
            value hash = $generate_hash_expression loc ctxt rc z0$ ;
           end)
          (struct
            type t = $z1$ ;
            value equal = $generate_eq_expression loc ctxt rc z1$ ;
            value hash = $generate_hash_expression loc ctxt rc z1$ ;
           end) ;
      value $lid:memo_fname$ f =
        let ht = $uid:mname$.create 251 in
        fun ( x : $z0$ ) ( y : $z1$ ) ->
          try $uid:mname$.find ht (x,y)
          with [ Not_found -> do {
            let newv = f x y in 
            $uid:mname$.add ht (x,y) newv ;
            newv
          }]
        ;
      end
     >>

  | Right l ->
    let vars_types = List.mapi (fun i x -> (Printf.sprintf "v_%d" i, x)) l in
    let (hc_args, prim_args) = filter_split (fun (_, (x, _)) -> x) vars_types in do {
      assert (hc_args <> []) ;
      if prim_args <> [] then
        let hc_memo_name = find_matching_memo loc rc (List.map snd hc_args) in
        let prim_memo_name = find_matching_memo loc rc (List.map snd prim_args) in
        let hc_mname = "HT_"^hc_memo_name in
        let prim_mname = "HT_"^prim_memo_name in

        let hc_function_expr =
          Expr.abstract_over (List.map (to_typatt loc) hc_args)
            <:expr< $uid:prim_mname$.create 251 >> in

        let hc_function_call =
          Expr.applist <:expr< hc_f >> (List.map (to_expr loc) hc_args) in

        let f_call = Expr.applist <:expr< f >> (List.map (to_expr loc) vars_types) in
        let prim_function_expr =
          Expr.abstract_over (List.map (to_typatt loc) prim_args) f_call in
        
        let prim_memo_call =
          Expr.applist <:expr< $lid:prim_memo_name$ >>
            [prim_function_expr; <:expr< ht >> :: List.map (to_expr loc) prim_args] in
                               
        let hc_call = Expr.applist <:expr< hc_f >> (List.map (to_expr loc) hc_args) in

        let fun_body =
          Expr.abstract_over (List.map (to_typatt loc) vars_types)
          <:expr< let ht = $hc_call$ in
                  $prim_memo_call$ >> in

        <:str_item<
          value $lid:memo_fname$ f =
            let hc_f = $lid:hc_memo_name$ $hc_function_expr$ in
            $fun_body$
        >>
      else match hc_args with [
        []|[_]|[_;_] -> assert False
        | [arg1; arg2 :: rest] ->
        let first_memo_name = find_matching_memo loc rc (List.map snd [arg1;arg2]) in
        let pairty = <:ctyp< ( $list:[to_ctyp arg1;to_ctyp arg2]$ ) >> in
        let second_memo_name = find_matching_memo loc rc [(True, pairty) :: List.map snd rest] in
        let first_mname = "HT_"^first_memo_name in
        let second_mname = "HT_"^second_memo_name in

        let second_f_call =
          Expr.applist <:expr< second_f p >> (List.map (to_expr loc) rest) in
        let body = <:expr<
                     let p = first_f $to_expr loc arg1$ $to_expr loc arg2$ in
                     $second_f_call$ >> in
        let fun_body =
          Expr.abstract_over (List.map (to_typatt loc) hc_args) body in
        
        let f_call = Expr.applist <:expr< f >> (List.map (to_expr loc) hc_args) in
        let second_f_function =
          Expr.abstract_over [<:patt< ($to_patt loc arg1$, $to_patt loc arg2$) >> :: List.map (to_patt loc) rest]
            f_call in
        <:str_item<
          value $lid:memo_fname$ f =
            let first_f = $lid:first_memo_name$ (fun a1 a2 -> (a1, a2)) in
            let second_f = $lid:second_memo_name$
              $second_f_function$ in
            $fun_body$
          >>
      ]
    }

  ]
;

(*
value generate_memo_ephemeron_modules loc ctxt rc memo_fname bindings =
  let rec genrec = fun [
    [(i, _, ty)] ->
    let loc = loc_of_ctyp ty in
    let mname = Printf.sprintf "HT%d_%s" i memo_fname in
    [<:str_item<
    module $mname$ = Ephemeron.K1.Make(struct
        type t = $ty$ ;
        value equal = $generate_eq_expression loc ctxt rc ty$ ;
        value hash = $generate_hash_expression loc ctxt rc ty$ ;
      end)
    >>
    ]
  | [(_, _, ty1); (j, _, ty2) :: rest] ->
    let loc = loc_of_ctyp ty2 in
    let mname = Printf.sprintf "HT%d_%s" j memo_fname in
    [<:str_item<
    module $mname$ = Ephemeron.K2.Make(struct
        type t = $ty1$ ;
        value equal = $generate_eq_expression loc ctxt rc ty1$ ;
        value hash = $generate_hash_expression loc ctxt rc ty1$ ;
      end)
     (struct
        type t = $ty2$ ;
        value equal = $generate_eq_expression loc ctxt rc ty2$ ;
        value hash = $generate_hash_expression loc ctxt rc ty2$ ;
      end)
    >>
    :: (if rest = [] then [] else genrec [ (-1, "", <:ctyp:< ( $ty1$ * $ty2$ ) >>) :: rest])
   ]
  ] in
  genrec bindings
;

value generate_memo_ephemeron_bindings loc ctxt rc memo_fname bindings =
  let rec genrec = fun [
    [(i, _, ty)] ->
    let loc = loc_of_ctyp ty in
    let mname = Printf.sprintf "HT%d_%s" i memo_fname in
    let htname = Printf.sprintf "ht%d_%s" i memo_fname in
    [(<:patt< $lid:htname$ >>, <:expr< $uid:mname$.create 251 >>, <:vala< [] >>)
    ]
  | [(_, _, ty1); (j, _, ty2) :: rest] ->
    let loc = loc_of_ctyp ty2 in
    let mname = Printf.sprintf "HT%d_%s" j memo_fname in
    let htname = Printf.sprintf "ht%d_%s" j memo_fname in
    [(<:patt< $lid:htname$ >>, <:expr< $uid:mname$.create 251 >>, <:vala< [] >>)
    :: (if rest = [] then [] else genrec [ (-1, "", <:ctyp:< ( $ty1$ * $ty2$ ) >>) :: rest])
   ]
  ] in
  genrec bindings
;

value generate_memo_hash_modules loc ctxt rc memo_fname bindings =
  if bindings = [] then [] else
  let types = List.map (fun (_, _, ty) -> ty) bindings in
  let ((i, _, _), _) = sep_last bindings in
  let ty = match types with [
    [ty] -> ty
  | [ _ :: _ ] -> <:ctyp< ( $list:types$ ) >>
  ] in
  let mname = Printf.sprintf "HT%d_%s" i memo_fname in
  [<:str_item<
    module $mname$ = Hashtbl.Make(struct
      type t = $ty$ ;
      value equal = $generate_eq_expression loc ctxt rc ty$ ;
      value hash = $generate_hash_expression loc ctxt rc ty$ ;
    end)
    >>
  ]
;

value generate_memo_hash_binding loc ctxt rc memo_fname bindings = do {
  assert (bindings <> []) ;
  let ((i, _, _), _) = sep_last bindings in
  let mname = Printf.sprintf "HT%d_%s" i memo_fname in
  let htname = Printf.sprintf "ht%d_%s" i memo_fname in
  <:str_item< value $lid:htname$ = $uid:mname$.create 251 >>
}
;

value preprocess_memo_arguments loc ctxt rc (memo_fname, memo_tys) =
  let arg_bindings = List.mapi (fun i ty -> (i, Printf.sprintf "v_%d" i, ty)) memo_tys in
  let pred = fun [
    (_, _, <:ctyp< $lid:lid$ >>) when List.mem_assoc lid rc.type_decls -> True
  | (_, _, z) when List.mem (canon_ctyp z) builtin_types -> False
  | (_, _, z) -> Ploc.raise (loc_of_ctyp z)
      (Failure Fmt.(str "generate_memo_items %s: types can only be either primitive or hashconsed: %a"
                      memo_fname Pp_MLast.pp_ctyp z))
  ] in
  let (hc_bindings, prim_bindings) = filter_split pred arg_bindings in
  if hc_bindings = [] then
    Ploc.raise loc (Failure Fmt.(str "generate_memo_items %s: no hashconsed types specified" memo_fname))
  else
    (arg_bindings, hc_bindings, prim_bindings)
;

value generate_memo_items loc ctxt rc (memo_fname, memo_tys) =
  let (arg_bindings, hc_bindings, prim_bindings) = 
    preprocess_memo_arguments loc ctxt rc (memo_fname, memo_tys) in
  let ephemeron_si_modules = generate_memo_ephemeron_modules loc ctxt rc memo_fname hc_bindings in
  let hash_si_modules = generate_memo_hash_modules loc ctxt rc memo_fname prim_bindings in
  ephemeron_si_modules @ hash_si_modules
;

value generate_memo_function_prim_expression loc ctxt rc memo_fname prim_bindings recompute_expr = do {
  assert (prim_bindings <> []) ;
  let vars = List.map (fun (_, v, _) -> v) prim_bindings in
  let vars_exps = List.map (fun v -> <:expr< $lid:v$ >>) vars in
  let keyexp = match vars_exps with [
    [e] -> e
  | _ -> <:expr< ( $list:vars_exps$ ) >>
  ] in
  let ((i, _, _), _) = sep_last prim_bindings in
  let mname = Printf.sprintf "HT%d_%s" i memo_fname in
  <:expr< (fun __ht__ ->
    try $uid:mname$.find __ht__ $keyexp$
    with [Not_found -> 
      let __newval__ = $recompute_expr$ in do {
        $uid:mname$.add __ht__ $keyexp$ __newval__ ;
        __newval__
      }
          ]) >>
}
;

value generate_memo_function_prim_constructor loc ctxt rc memo_fname prim_bindings = do {
  assert (prim_bindings <> []) ;
  let ((i, _, _), _) = sep_last prim_bindings in
  let mname = Printf.sprintf "HT%d_%s" i memo_fname in
  <:expr< $uid:mname$.create 251 >>
}
;

value generate_memo_function_body loc ctxt rc (memo_fname, memo_tys) =
  let (arg_bindings, hc_bindings, prim_bindings) = 
    preprocess_memo_arguments loc ctxt rc (memo_fname, memo_tys) in
  let recompute_exp = Expr.applist <:expr< f >> (List.map (fun (_, v, _) -> <:expr< $lid:v$ >>) arg_bindings) in

  let rec genrec = fun [
    [] -> Ploc.raise loc (Failure Fmt.(str "generate_memo_function_body: must supply some hashconsed types"))
  | [(i, v, ty)] ->
    let mname = Printf.sprintf "HT%d_%s" i memo_fname in
    let htname = Printf.sprintf "ht%d_%s" i memo_fname in
    if prim_bindings = [] then
      <:expr<
      try $uid:mname$.find $lid:htname$ $lid:v$
      with [ Not_found -> do {
        let __newval__ = __recompute_expr__ () in
          $uid:mname$.add $lid:htname$ $lid:v$ __newval__ ;
          __newval__
        }]
      >>
    else
      let prim_e =
        generate_memo_function_prim_expression loc ctxt rc memo_fname prim_bindings <:expr< __recompute_expr__ () >> in
      let prim_ce = generate_memo_function_prim_constructor loc ctxt rc memo_fname prim_bindings in
      let v_ht = Printf.sprintf "ht_%s" v in
      <:expr<
      let $lid:v_ht$ =
        try $uid:mname$.find $lid:htname$ $lid:v$
        with [ Not_found -> do {
          let $lid:v_ht$ = $prim_ce$ in
          $uid:mname$.add $lid:htname$ $lid:v$ $lid:v_ht$ ;
          $lid:v_ht$
        }] in
        $prim_e$ $lid:v_ht$
      >>

  | [(_, v1, ty1) ; (j, v2, ty2)] ->
    let mname = Printf.sprintf "HT%d_%s" j memo_fname in
    let htname = Printf.sprintf "ht%d_%s" j memo_fname in
    if prim_bindings = [] then
      <:expr<
      try $uid:mname$.find $lid:htname$ ($lid:v1$, $lid:v2$)
      with [ Not_found -> do {
        let __newval__ = __recompute_expr__ () in
          $uid:mname$.add $lid:htname$ ($lid:v1$, $lid:v2$) __newval__ ;
          __newval__
        }]
      >>
    else
      let prim_e =
        generate_memo_function_prim_expression loc ctxt rc memo_fname prim_bindings <:expr< __recompute_expr__ () >> in
      let prim_ce = generate_memo_function_prim_constructor loc ctxt rc memo_fname prim_bindings in
      let v_ht = Printf.sprintf "ht_%s" v2 in
      <:expr<
      let $lid:v_ht$ =
        try $uid:mname$.find $lid:htname$ ($lid:v1$, $lid:v2$)
        with [ Not_found -> do {
          let $lid:v_ht$ = $prim_ce$ in
          $uid:mname$.add $lid:htname$ ($lid:v1$, $lid:v2$) $lid:v_ht$ ;
          $lid:v_ht$
        }] in
        $prim_e$ $lid:v_ht$
      >>
  ] in
  let hc_exp = genrec hc_bindings in
  <:expr<
    let __recompute_expr__ = fun () -> $recompute_exp$ in
    $hc_exp$
  >>
;

value generate_memo_function_binding loc ctxt rc (memo_fname, memo_tys) =
  let (arg_bindings, hc_bindings, prim_bindings) = 
    preprocess_memo_arguments loc ctxt rc (memo_fname, memo_tys) in
  let body =
    List.fold_right (fun (_, v, ty) rhs -> <:expr< fun ($lid:v$ : $ty$) -> $rhs$ >>)
      arg_bindings (generate_memo_function_body loc ctxt rc (memo_fname, memo_tys)) in
  let e = <:expr< fun f ->
    let $list:generate_memo_ephemeron_bindings loc ctxt rc memo_fname hc_bindings$ in
    $body$
    >> in
  let e = canon_expr e in
  (<:patt< $lid:memo_fname$ >>, e, <:vala< [] >>)
;
*)

value hashcons_module_name (name, td) =
  match List.find_map (fun a ->
      match uv a with [
        <:attribute_body< hashcons_module $uid:mname$ ; >> -> Some mname
      | _ -> None
      ]) (uv td.tdAttributes) with [
    Some n -> n
  | None -> "HC_"^name
  ]
;

value hashcons_constructor_name (name, td) =
  match List.find_map (fun a ->
      match uv a with [
        <:attribute_body< hashcons_constructor $lid:cname$ ; >> -> Some cname
      | _ -> None
      ]) (uv td.tdAttributes) with [
    Some n -> n
  | None -> "make_"^name
  ]
;

value generate_hashcons_module ctxt rc (name, td) =
  let loc = loc_of_type_decl td in
  let modname = hashcons_module_name (name, td) in
  let node_name = name^"_node" in
  let pre_eq_name = "preeq_"^name^"_node" in
  let pre_hash_name = "prehash_"^name^"_node" in
  <:str_item< module $uid:modname$ = Hashcons.Make(struct
              type t = $lid:node_name$ ;
              value equal = $lid:pre_eq_name$ ;
              value hash = $lid:pre_hash_name$ ;
              end) >>
;

value generate_hashcons_constructor ctxt rc (name, td) =
  let loc = loc_of_type_decl td in
  let modname = hashcons_module_name (name, td) in
  let consname = hashcons_constructor_name (name, td) in
  let htname = name^"_ht" in
  <:str_item< declare
                 value $lid:htname$ = $uid:modname$.create 10007 ;
                 value $lid:consname$ x = $uid:modname$.hashcons $lid:htname$ x ;
              end >>
;

end
;

value hashconsed_type_decl ctxt td =
  let loc = loc_of_type_decl td in
  let name = td.tdNam |> uv |> snd |> uv in
  let data_name = name^"_node" in
  let tyargs =
    let tyvars = td.tdPrm |> uv in
    List.map (fun [
        (<:vala< None >>, _) ->
        Ploc.raise loc (Failure Fmt.(str "hashconsed_type_decl: %s: formal type-vars must all be named"
                                       name))
      | (<:vala< Some id >>, _) -> <:ctyp< ' $id$ >>
      ]) tyvars in
  let hc_tdDef =
    let data_type = <:ctyp< $lid:data_name$ >> in
    <:ctyp< hash_consed $Ctyp.applist data_type tyargs$ >> in
  [ { (td) with tdNam =
                let n = <:vala< data_name >> in
                <:vala< (loc, n) >> }
  ; <:type_decl< $lid:name$ $_list:td.tdPrm$ = $hc_tdDef$ >>
  ]
;

value str_item_gen_hashcons name arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> ->
    let rc = HC.build_context loc arg tdl in
    let ll = List.map (hashconsed_type_decl arg) tdl in
    let new_tdl =
      let tdl = List.concat ll in
      tdl @ [
        <:type_decl< hash_consed +'a = Hashcons.hash_consed 'a == private {
                     hkey : int;
                     tag : int;
                     node : 'a } >> 
      ] in
    let pre_eq_bindings = List.map (HC.generate_pre_eq_binding arg rc) rc.HC.type_decls in
    let pre_hash_bindings = List.map (HC.generate_pre_hash_binding arg rc) rc.HC.type_decls in
    let hashcons_modules = List.map (HC.generate_hashcons_module arg rc) rc.HC.type_decls in
    let hash_bindings = List.concat (List.map (HC.generate_hash_bindings arg rc) rc.HC.type_decls) in
    let hashcons_constructors = List.map (HC.generate_hashcons_constructor arg rc) rc.HC.type_decls in
    let memo_items = List.map (HC.generate_memo_item loc arg rc) rc.HC.memo in
    let memo_items = List.map (Reloc.str_item (fun _ -> Ploc.dummy) 0) memo_items in
    <:str_item< module $uid:rc.module_name$ = struct
                open Hashcons ;
                type $list:new_tdl$ ;
                value $list:pre_eq_bindings$ ;
                value $list:pre_hash_bindings$ ;
                declare $list:hashcons_modules @ hashcons_constructors$ end ;
                value $list:hash_bindings$ ;
                declare $list:memo_items$ end ;
                  end >>
| _ -> assert False ]
;

Pa_deriving.(Registry.add PI.{
  name = "hashcons"
; alternates = []
; options = ["optional"; "module_name"; "memo"]
; default_options = let loc = Ploc.dummy in [ ("optional", <:expr< False >>) ]
; alg_attributes = []
; expr_extensions = []
; ctyp_extensions = []
; expr = (fun arg e -> assert False)
; ctyp = (fun arg e -> assert False)
; str_item = str_item_gen_hashcons
; sig_item = (fun arg e -> assert False)
})
;

