(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* initialization types and basic operations over these types *)

open Misc
open Deftypes
open Definit
open Global
       
(** a set of initialization names *)
module S = struct
  include (Set.Make(Definit))
  let fprint_t ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun e -> Format.fprintf ff "%a@ " Pinit.init e) s;
    Format.fprintf ff "}@]"
end

(* a module to represent the set of predecessors/successors of a variable *)
module M = struct
  include (Map.Make(Definit))
  let fprint_t fprint_v ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun k v -> Format.fprintf ff "%a->%a@ " Pinit.init k fprint_v v) s;
    Format.fprintf ff "}@]"
end

let fprint_t = S.fprint_t
let fprint_tt = M.fprint_t S.fprint_t

(* typing errors *)
type error = Iless_than
      
exception Clash of error

let new_var () = 
  { i_desc = Ivar; i_index = symbol#name; i_level = !binding_level;
    i_inf = []; i_sup = []; i_visited = -1; 
    i_useful = false; i_polarity = Punknown; i_min = Izero }
let ivalue v = 
  { i_desc = Ivalue(v); i_index = symbol#name; i_level = generic;
    i_inf = []; i_sup = [];
    i_visited = -1; i_useful = false; i_polarity = Punknown; i_min = Izero }
let ione = ivalue Ione
let ihalf = ivalue Ihalf
let izero = ivalue Izero
let funtype ti1 ti2 = Ifun(ti1, ti2)
let rec funtype_list ti_arg_list ti_res =
  match ti_arg_list with
  | [] -> ti_res
  | [ti] -> funtype ti ti_res
  | ti :: ti_arg_list -> funtype ti (funtype_list ti_arg_list ti_res)
let product l = Iproduct(l)
let atom i = Iatom(i)
    
(* basic operation on initialization values *)
let rec irepr i =
  match i.i_desc with
    | Ilink(i_son) ->
        let i_son = irepr i_son in
        i.i_desc <- Ilink(i_son);
        i_son
    | _ -> i

(* equality of two initialization tags *)
let equal i1 i2 =
  let i1 = irepr i1 in
  let i2 = irepr i2 in
  if i1 == i2 then true
  else match i1.i_desc, i2.i_desc with
    | Ivalue(v1), Ivalue(v2) -> v1 = v2
    | Ivar, Ivar -> i1.i_index = i2.i_index
    | _ -> false
    
let rec add i l =
  match l with
  | [] -> [i]
  | i1 :: l1 -> if equal i i1 then l else i1 :: (add i l1)

let rec remove i l =
  match l with
  | [] -> []
  | i1 :: l1 -> if equal i i1 then l1 else i1 :: (remove i l1)

let rec union l1 l2 = 
  let rec mem i l =
    match l with | [] -> false | i1 :: l -> (equal i i1) || (mem i l) in
  match l1, l2 with
  | [], l2 -> l2 | l1, [] -> l1
  | i :: l1, l2 -> if mem i l2 then union l1 l2 else i :: union l1 l2
                                                              
let set l = List.fold_left (fun acc c -> add c acc) [] l

(** Sets the polarity of a type. *)
let polarity_c i right =
  match i.i_polarity, right with
  | Punknown, true -> i.i_polarity <- Pplus
  | Punknown, false -> i.i_polarity <- Pminus
  | Pminus, true | Pplus, false -> i.i_polarity <- Pplusminus
  | _ -> ()

let increase_polarity p i =
  match p with
  | Punknown -> i.i_polarity <- p
  | _ -> if p <> i.i_polarity then i.i_polarity <- Pplusminus
      
(* saturate an initialization type [i]. *)
(* on the right, [i] and all types [j] such that [i < j] are replaced by 1. *)
(* on the left, [i] and all types [j] such that [j < i] are replaced *)
(* by 0 if the min of [i] is 0. If it is 1/2, [i < 1/2] *)
let rec saturate_i is_right i =
  let i = irepr i in
  let iv = if is_right then Ione else Izero in
  match i.i_desc with
  | Ivalue(i) when i = iv -> ()
  | Ivar ->
      if i.i_min = Ihalf && not is_right then i.i_sup <- add ihalf i.i_sup
        else begin
          i.i_desc <- Ilink(ivalue iv);
          List.iter
            (saturate_i is_right) (if is_right then i.i_sup else i.i_inf)
        end
  | Ilink(i) -> saturate_i is_right i
  | _ -> raise (Clash(Iless_than))
  
and less_v v1 v2 =
  match v1, v2 with
  | (Izero, _) | (_, Ione) | (Ihalf, Ihalf) -> true
  | _ -> false
    
(** Sub-typing *)
let rec less left_ti right_ti =
  if left_ti == right_ti then ()
  else
    match left_ti, right_ti with
    | Ifun(ti1, ti2), Ifun(ti3, ti4) ->
       less ti2 ti4; less ti3 ti1
    | Iproduct(l1), Iproduct(l2) -> List.iter2 less l1 l2
    | Iatom(i1), Iatom(i2) -> less_i i1 i2
    | _ -> raise (Clash(Iless_than))

and less_i left_i right_i =
  if left_i == right_i then ()
  else
    let left_i = irepr left_i in
    let right_i = irepr right_i in
    if left_i == right_i then ()
    else
      match left_i.i_desc, right_i.i_desc with
      | (Ivalue(Izero), _) | (_, Ivalue(Ione))
      | (Ivalue(Ihalf), Ivalue(Ihalf)) -> ()
      | Ivalue(Ihalf), Ivar ->
          right_i.i_inf <- add left_i right_i.i_inf
      | Ivar, Ivalue(Ihalf) ->
          left_i.i_sup <- add right_i left_i.i_sup
      | Ivalue(Ione), Ivar -> saturate_i true right_i
      | Ivar, Ivalue(Izero) -> saturate_i false left_i
      | Ivar, Ivar ->
          (* i1,...,in < i < j1,...,jk  with  *)
          (* l1,...,lm < r < s1,...,sr *)
          right_i.i_inf <- add left_i right_i.i_inf;
          left_i.i_sup <- add right_i left_i.i_sup
      | _ -> raise (Clash(Iless_than))
               
(** Computing an initialization type from a type *)
let rec skeleton { t_desc = desc } =
  match desc with
  | Tvar -> atom (new_var ())
  | Tfun(_, _, ti1, ti2) -> funtype (skeleton ti1) (skeleton ti2)
  | Tproduct(ti_list) -> product (List.map skeleton ti_list)
  | Tconstr(_, _, _) | Tvec _ -> atom (new_var ())
  | Tlink(ti) -> skeleton ti
                          
let rec skeleton_on_i i { t_desc = desc } =
  match desc with
  | Tvar -> atom i
  | Tfun(_, _, ti1, ti2) ->
     funtype (skeleton_on_i i ti1) (skeleton_on_i i ti2)
  | Tproduct(ti_list) -> product (List.map (skeleton_on_i i) ti_list)
  | Tconstr(_, _, _) | Tvec _ -> atom i
  | Tlink(ti) -> skeleton_on_i i ti

(* For external values, the skeleton type is over constrained *)
(* only combinatorial function get a polymorphic type signature. *)
(* others must have all their inputs/outputs initialized *)
(* This function is not used for the moment as it would *)
(* prevent to write [x = pre(x)] *)
(*
let skeleton_for_external_values ty =
  let rec skeleton_on_i i { t_desc = desc } =
    match desc with
    | Tvar -> atom i
    | Tfun(k, _, ti1, ti2) ->
        let i = match k with Tany | Tstatic _ -> i | _ -> izero in
        funtype (skeleton_on_i i ti1) (skeleton_on_i i ti2)
    | Tproduct(ti_list) -> product (List.map (skeleton_on_i i) ti_list)
    | Tconstr(_, _, _) | Tvec _ -> atom i
    | Tlink(ti) -> skeleton_on_i i ti in
  let i = new_var () in
  skeleton_on_i i ty
*)
                   
let rec fresh_on_i i ti =
  match ti with
  | Ifun(left_ti, right_ti) ->
      funtype (fresh_on_i i left_ti) (fresh_on_i i right_ti)
  | Iproduct(ti_list) -> product (List.map (fresh_on_i i) ti_list)
  | Iatom _ -> atom i
                 
(* Compute the infimum/supremum of two types *)
let rec suptype is_right ti1 ti2 =
  match ti1, ti2 with
  | Ifun(left_ti1, right_ti1), Ifun(left_ti2, right_ti2) ->
    Ifun(suptype (not is_right) left_ti1 left_ti2,
         suptype is_right right_ti1 right_ti2)
  | Iproduct(ti_list1), Iproduct(ti_list2) ->
    let ti_list =
      try List.map2 (suptype is_right) ti_list1 ti_list2
      with Invalid_argument _ -> assert false in
    Iproduct(ti_list)
  | Iatom(i1), Iatom(i2) -> Iatom(sup_i is_right i1 i2)
  | _ -> assert false

and sup_i is_right i1 i2 =
  let i1 = irepr i1 in
  let i2 = irepr i2 in
  if i1 == i2 then i1
  else
    match i1.i_desc, i2.i_desc, is_right with
    | Ivalue(Izero), _, true -> i2 | _, Ivalue(Izero), true -> i1
    | (Ivalue(Ione), _, true) | (_, Ivalue(Ione), true) -> ione
    | Ivalue(Ione), _, false -> i2 | _, Ivalue(Ione), false -> i1
    | (Ivalue(Izero), _, false) | (_, Ivalue(Izero), false) -> izero
    | (Ivalue(Ihalf), Ivalue(Ihalf), _) -> ihalf
    | Ilink(i1), _ , _ -> sup_i is_right i1 i2
    | _, Ilink(i2), _ -> sup_i is_right i1 i2
    | _ -> let i = new_var () in
        if is_right then i.i_inf <- [i1; i2] else i.i_sup <- [i1; i2]; i

(* visit a type; [visit v ti] recursively mark *)
(* all nodes with value [v] *) 
let rec visit v ti =
  match ti with
  | Ifun(ti1, ti2) -> visit v ti1; visit v ti2
  | Iproduct(ti_list) -> List.iter (visit v) ti_list
  | Iatom(i) -> visit_i v i

and visit_i v i =
  match i.i_desc with
  | Ivar ->
      i.i_visited <- v;
      List.iter (visit_i v) i.i_inf;
      List.iter (visit_i v) i.i_sup
  | Ivalue _ -> ()
  | Ilink(i) -> visit_i v i
                  
(** Mark useful/useless types and sets the polarity *)
(* reduces dependences by eliminating intermediate variables *)
(* we first mark useful variables (variables which appear in *)
(* the final type. We also compute polarities *)
let rec mark right ti =
  match ti with
  | Ifun(ti1, ti2) -> mark right ti2; mark (not right) ti1
  | Iproduct(ti_list) -> List.iter (mark right) ti_list
  | Iatom(i) -> imark right i

and imark right i =
  let i = irepr i in
  match i.i_desc with
  | Ivar ->
      i.i_useful <- true;
      polarity_c i right
  | Ivalue _ | Ilink _ -> ()
                              
(* Garbage collection: only keep dependences of the form a- < b+ *)
(* this step is done after having called the function mark *)
let rec shorten ti =
  match ti with
  | Ifun(ti1, ti2) -> shorten ti1; shorten ti2
  | Iproduct(ti_list) -> List.iter shorten ti_list
  | Iatom(i) -> shorten_i i

and shorten_i i =
  let i = irepr i in
  match i.i_desc with
  | Ivalue _ -> ()
  | Ilink(i) -> shorten_i i
  | Ivar ->
     i.i_visited <- 0;
     (* only keep a dependence a- < b+ *)
     let inf, sup =
       match i.i_polarity with
       | Punknown -> assert false
       | Pplus -> remove_polarity Pplus (short_list false [] i.i_inf), []
       | Pminus -> [], remove_polarity Pminus (short_list true [] i.i_sup)
       | Pplusminus ->
         short_list false [] i.i_inf, short_list true [] i.i_sup in
     i.i_inf <- inf;
     i.i_sup <- sup;
     i.i_visited <- 1
      
                      
and short_list is_right acc i_list =
  List.fold_left (short is_right) acc i_list

(* only keep a dependence a- < b+ *)
and remove_polarity p i_list =
  let clear acc i_right =
    match p, i_right.i_polarity with
    | (Pplus, Pplus) | (Pminus, Pminus) -> acc
    | _ -> i_right :: acc in
  List.fold_left clear [] i_list
    
and short is_right acc i =
  match i.i_desc with
  | Ivalue(Izero | Ione) -> acc
  | Ivalue _ -> add i acc
  | Ilink(i) -> short is_right acc i
  | Ivar ->
    match i.i_visited with
    | -1 -> (* never visited *)
      i.i_visited <- 0;
      let acc =
        short_list is_right acc (if is_right then i.i_sup else i.i_inf) in
      let acc = if i.i_useful then add i acc else acc in
      i.i_visited <- -1;
      acc
    | 0 -> (* currently visited *)
      acc
    | _ -> (* visited in a previous pass *) 
      (* the variable is added only if it is useful *)
      if i.i_useful then add i acc else union i.i_inf acc  

                              
(* Final simplification. *)
(*- a variable a+ which has no inf. can be replaced by 0;
 *- a variable a- which has no sup. can be replaced by 1;
 *- if a- has a single sup. b+, it can be replaced by it
 *- if a+ has a single inf. b-, it can be replaced by it. *)
let rec simplify right ti =
  match ti with
  | Ifun(ti1, ti2) -> funtype (simplify (not right) ti1) (simplify right ti2)
  | Iproduct(ti_list) -> product(List.map (simplify right) ti_list)
  | Iatom(i) -> Iatom(isimplify right i)

and isimplify right i =
  let i = irepr i in
  match i.i_desc with
  | Ivalue _ | Ilink _ -> i
  | Ivar ->
    if right then
      match i.i_inf, i.i_polarity with
      | [], Pplus -> izero
      | [i_inf], Pplus ->
        increase_polarity Pplus i_inf;
        i.i_useful <- false; i_inf
      | _ -> i
    else
      match i.i_sup, i.i_polarity with
      | [], Pminus -> ione
      | [i_sup], Pminus ->
          increase_polarity Pminus i_sup;
          i.i_useful <- false; i_sup
      | _ -> i
      
(** Generalisation of a type *)
(* the level of generalised type variables *)
(* is set to [generic]. Returns [generic] when a sub-term *)
(* can be generalised *)
let list_of_vars = ref []
                       
let rec gen ti =
  match ti with
  | Ifun(ti1, ti2) -> gen ti1; gen ti2
  | Iproduct(ti_list) -> List.iter gen ti_list
  | Iatom(i) -> ignore (igen i)
                       
and igen i =
  let i = irepr i in
  match i.i_desc with
  | Ivalue _ -> i.i_level
  | Ivar ->
    if i.i_level > !binding_level
    then 
      begin
        i.i_level <- generic;
        let level1 = gen_set i.i_inf in
        let level2 = gen_set i.i_sup in
        let level = min level1 level2 in
        i.i_level <- level;
        if level = generic then list_of_vars := i :: !list_of_vars
      end;
    i.i_level
  | Ilink(link) -> igen link
                        
and gen_set l = List.fold_left (fun acc i -> max (igen i) acc) generic l
                               
(** Computes the dependence relation from a list of initialisation variables *)
(* variables in [already] are disgarded *)
let relation i_list =
  let rec relation (already, rel) i =
    let i = irepr i in
    if S.mem i already then already, rel
    else if i.i_sup = [] then already, rel
    else List.fold_left
           relation (S.add i already, (i, set i.i_sup) :: rel) i.i_sup in
  let _, rel =
    List.fold_left (fun acc i -> relation acc i) (S.empty, []) i_list in
  rel

(** Main generalisation function *)
let generalise ti =
  list_of_vars := [];
  (* we mark useful variables *)
  mark true ti;
  (* garbage collect dependences *)
  shorten ti;
  let ti = simplify true ti in
  mark true ti;
  shorten ti;
  gen ti;
  let rel = relation !list_of_vars in
  { typ_vars = !list_of_vars; typ_rel = rel; typ = ti }

(** Instantiation of a type *)
(* save and cleanup links *)
let links = ref []
    
let save link = links := link :: !links
let cleanup () = List.iter (fun i -> i.i_desc <- Ivar) !links; links := []
                                                                          
(* makes a copy of the type scheme *)
let rec copy ti =
  match ti with
  | Ifun(ti1, ti2) -> funtype (copy ti1) (copy ti2)
  | Iproduct(ti_list) -> product (List.map copy ti_list)
  | Iatom(i) -> atom (icopy i)

and icopy i =
  match i.i_desc with
  | Ivar ->
     if i.i_level = generic
     then
       let sup_list = List.map icopy i.i_sup in
       let v = { (new_var ()) with i_sup = sup_list } in
       i.i_desc <- Ilink(v);
       save i;
       v
     else i
  | Ilink(link) ->
     if i.i_level = generic then link else icopy link
  | Ivalue(v) ->
     if i.i_level = generic then ivalue v else i

(* instanciate the initialisation type according to the type *)
let rec instance ti ty =
  let { t_desc = t_desc } as ty = Types.typ_repr ty in
  match ti, t_desc with
  | Ifun(ti1, ti2), Tfun(_, _, ty1, ty2) ->
     funtype (instance ti1 ty1) (instance ti2 ty2)
  | Iproduct(ti_list), Tproduct(ty_list) ->
    begin try product (List.map2 instance ti_list ty_list)
      with | Invalid_argument _ -> assert false end
  | Iatom(i), _ -> skeleton_on_i i ty
  | _ -> assert false

(* subtyping. [subtype right ti = tj] with ti < tj if right, else tj < ti *)
let rec subtype right ti =
  match ti with
  | Ifun(ti1, ti2) ->
      funtype (subtype (not right) ti1) (subtype right ti2)
  | Iproduct(ti_list) ->
      begin try product (List.map (subtype right) ti_list)
        with | Invalid_argument _ -> assert false end
  | Iatom(i) ->
      let new_i = new_var () in
      if right then less_i i new_i else less_i new_i i;
      atom new_i

(* subtyping but the right one gets minimal bound 1/2 instead of 0 *)
let rec halftype right ti =
  match ti with
  | Ifun(ti1, ti2) ->
      funtype (halftype (not right) ti1) (halftype right ti2)
  | Iproduct(ti_list) ->
      begin try product (List.map (halftype right) ti_list)
        with | Invalid_argument _ -> assert false end
  | Iatom(i) ->
     atom (half_i right i)

and half_i right i =
  let new_i = { (new_var ()) with i_min = Ihalf } in
  if right then less_i i new_i else less_i new_i i; new_i

(* instanciation *)
let instance { typ = ti } ty =
  let ti = copy ti in
  cleanup ();
  let ti = subtype true ti in
  instance ti ty

(* type instance *)
let instance { value_init = tis_opt } ty =
  (* build a default signature *)
  let default ty =
    skeleton_on_i (new_var ()) ty in
  match tis_opt with
  | None -> 
      (* if no initialization signature is declared, *)
      (* a default one is built from the type signature *)
      subtype true (default ty)
  | Some(tis) -> instance tis ty

let filter_arrow ti =
  match ti with
  | Ifun(ti1, ti2) -> ti1, ti2
  | _ -> assert false

let filter_product ti =
  match ti with
  | Iproduct(ti_list) -> ti_list
  | _ -> assert false

(** An entry in the type environment *)
type tentry =
    { t_typ: Definit.ti; (* the init type [ty] of x *)
      t_last: Definit.t; (* v in [0, 1/2, 1] so that last x: ty[v] *)
    }
    
(* prints the typing environment *)
let penv ff env =
  (* print every entry in the typing environment *)
  let pentry ff (n, { t_typ = ti; t_last = i }) =
    Format.fprintf ff "@[%a: %a | %a@]"
      Printer.source_name n Pinit.ptype ti Pinit.init i in
  let env = Ident.Env.bindings env in
  Pp_tools.print_list_r pentry "{" ";" "}" ff env
