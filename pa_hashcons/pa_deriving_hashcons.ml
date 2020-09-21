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

module HC = struct
type t = {
  module_name : string
; type_decls : list (string * MLast.type_decl)
; memo : list (string * list MLast.ctyp)
}
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
        (<:patt< $lid:memo_fname$ >>, <:expr< [%typ: ( $list:l$ )] >>) -> (memo_fname, l)
      | (<:patt< $lid:memo_fname$ >>, <:expr< [%typ: $type:t$] >>) -> (memo_fname, [t])
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
    [<:str_item< value $lid:htname$ = $uid:mname$.create 251 >>
    ]
  | [(_, _, ty1); (j, _, ty2) :: rest] ->
    let loc = loc_of_ctyp ty2 in
    let mname = Printf.sprintf "HT%d_%s" j memo_fname in
    let htname = Printf.sprintf "ht%d_%s" j memo_fname in
    [<:str_item< value $lid:htname$ = $uid:mname$.create 251 >>
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

value generate_memo_hash_bindings loc ctxt rc memo_fname bindings =
  if bindings = [] then [] else
  let types = List.map (fun (_, _, ty) -> ty) bindings in
  let ((i, _, _), _) = sep_last bindings in
  let mname = Printf.sprintf "HT%d_%s" i memo_fname in
  let htname = Printf.sprintf "ht%d_%s" i memo_fname in
  [<:str_item< value $lid:htname$ = $uid:mname$.create 251 >>
  ]
;

value generate_memo_items loc ctxt rc (memo_fname, memo_tys) =
  let arg_bindings = List.mapi (fun i ty -> (i, Printf.sprintf "v_%d" i, ty)) memo_tys in
  let pred = fun [
    (_, _, <:ctyp< $lid:lid$ >>) when List.mem_assoc lid rc.type_decls -> True
  | (_, _, z) when List.mem (canon_ctyp z) builtin_types -> False
  | (_, _, z) -> Ploc.raise (loc_of_ctyp z)
      (Failure Fmt.(str "generate_memo_items: types can only be either primitive or hashconsed: %a"
                      Pp_MLast.pp_ctyp z))
  ] in
  let (hc_bindings, prim_bindings) = filter_split pred arg_bindings in
  if hc_bindings = [] then
    Ploc.raise loc (Failure "generate_memo_items: no hashconsed types specified")
  else
    let ephemeron_si_modules = generate_memo_ephemeron_modules loc ctxt rc memo_fname hc_bindings in
    let hash_si_modules = generate_memo_hash_modules loc ctxt rc memo_fname prim_bindings in
    ephemeron_si_modules @ hash_si_modules
;


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
        <:type_decl< hash_consed +'a = Hashcons.hash_consed 'a >> 
      ] in
    let pre_eq_bindings = List.map (HC.generate_pre_eq_binding arg rc) rc.HC.type_decls in
    let pre_hash_bindings = List.map (HC.generate_pre_hash_binding arg rc) rc.HC.type_decls in
    let hashcons_modules = List.map (HC.generate_hashcons_module arg rc) rc.HC.type_decls in
    let hash_bindings = List.concat (List.map (HC.generate_hash_bindings arg rc) rc.HC.type_decls) in
    let hashcons_constructors = List.map (HC.generate_hashcons_constructor arg rc) rc.HC.type_decls in
    let memo_items = List.concat (List.map (HC.generate_memo_items loc arg rc) rc.HC.memo) in
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

