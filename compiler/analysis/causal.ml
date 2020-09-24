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

(* Causality types and basic operations over these types *)

open Misc
open Ident
open Deftypes
open Defcaus
open Global
open Zelus

(** a set of causality names *)
module S = struct
  include (Set.Make(Defcaus))
  let fprint_t ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun e -> Format.fprintf ff "%a@ " Pcaus.caus e) s;
    Format.fprintf ff "}@]"
end

(* a module to represent values associated to a causality name *)
module M = struct
  include (Map.Make(Defcaus))
  let fprint_t fprint_v ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun k v -> Format.fprintf ff "%a->%a@ " Pcaus.caus k fprint_v v) s;
    Format.fprintf ff "}@]"
end
  
(* a module to represent values associated to sets of causality names *)
module K = Map.Make(S)
    
let fprint_t = S.fprint_t
let fprint_tt = M.fprint_t S.fprint_t
                           
type cycle = Defcaus.t list

type error = cycle

(* typing errors *)
exception Clash of error
                                       
let new_var () = 
  { c_desc = Cvar; c_index = symbol#name; c_level = !binding_level;
    c_inf = []; c_sup = []; c_useful = false; 
    c_polarity = Punknown; c_info = None; c_visited = -1 }
let new_var_with_info { c_info = i } = { (new_var ()) with c_info = i }
let new_gen_var () = 
  { c_desc = Cvar; c_index = symbol#name; c_level = !binding_level + 1;
    c_inf = []; c_sup = []; c_useful = false; 
    c_polarity = Punknown; c_info = None; c_visited = -1 }
let product l = Cproduct(l)
let funtype tc1 tc2 = Cfun(tc1, tc2)
let rec funtype_list tc_arg_list tc_res =
  match tc_arg_list with
  | [] -> tc_res
  | [tc] -> funtype tc tc_res
  | tc :: tc_arg_list ->
     funtype tc (funtype_list tc_arg_list tc_res)
let atom c = Catom(c)
  
(* path compression *)
let rec crepr c =
  match c.c_desc with
  | Clink(c_son) ->
     let c_son = crepr c_son in
     c.c_desc <- Clink(c_son);
     c_son
  | _ -> c
           
(* equality of two causality tags *)
(* must not physically change types ! *)
let rec equal c1 c2 =
  match c1.c_desc, c2.c_desc with
  | Cvar, Cvar -> c1.c_index = c2.c_index
  | Clink(c1), _ -> equal c1 c2
  | _, Clink(c2) -> equal c1 c2

let rec add c l = 
  match l with 
  | [] -> [c] 
  | c1 :: l1 -> if equal c c1 then l else c1 :: (add c l1)

let rec remove c l =
  match l with
  | [] -> []
  | c1 :: l1 -> if equal c c1 then l1 else c1 :: (remove c l1)

let rec mem c l =
  match l with | [] -> false | c1 :: l -> (equal c c1) || (mem c l)

let rec union l1 l2 = 
  match l1, l2 with
  | [], l2 -> l2 | l1, [] -> l1
  | c :: l1, l2 -> if mem c l2 then union l1 l2 else c :: union l1 l2

let set l = List.fold_left (fun acc c -> add c acc) [] l
                      
(* sups *)
let sups c = let c = crepr c in c.c_sup
let allsups acc c =
  let rec allsups acc c =  add c (all_sups_list acc c.c_sup)
  and all_sups_list acc l = List.fold_left allsups acc l in
  all_sups_list acc (sups c)
    
let rec annotate n = function
  | Catom(c) -> atom(cannotate n c)
  | Cproduct(ty_list) -> product(List.map (annotate n) ty_list)
  | Cfun _ as ty -> ty
and cannotate n c =
  let c = crepr c in
  c.c_info <- Some(n); c

(* The set of variables of a causality type *)
let rec vars acc = function
  | Catom(c) -> vars_c acc c
  | Cproduct(ty_list) -> List.fold_left vars acc ty_list
  | Cfun(ty_arg, ty_res) -> vars (vars acc ty_arg) ty_res

and vars_c acc c = S.add (crepr c) acc
    
(** Sets the polarity of a type. *)
let rec polarity right tc =
  match tc with
  | Cfun(tc1, tc2) ->
     polarity (not right) tc1; polarity right tc2
  | Cproduct(tc_list) -> List.iter (polarity right) tc_list
  | Catom(c) -> polarity_c right c

and polarity_c right c =
  let c = crepr c in
  match c.c_polarity, right with
    | Punknown, true -> c.c_polarity <- Pplus
    | Punknown, false -> c.c_polarity <- Pminus
    | Pminus, true | Pplus, false -> c.c_polarity <- Pplusminus
    | _ -> ()

let increase_polarity p c =
  match p with
  | Punknown -> c.c_polarity <- p
  | _ -> if p <> c.c_polarity then c.c_polarity <- Pplusminus

(** check for cycles. Does [left_c] appears in [right_c] and its *)
(* greater elements *)
let rec occur_check ({ c_level = level; c_index = index } as c_left) c_right =
  let rec check path c_right =
    match c_right.c_desc with
    | Cvar -> 
       if c_right.c_level > level then c_right.c_level <- level;
       if c_right.c_index = index 
       then raise (Clash(List.rev path))
       else List.iter (check (c_right :: path)) c_right.c_sup
    | Clink(link) -> check path link
  in check [c_left] c_right

(* For debug purpose only *)
let rec check_type tc =
  match tc with
  | Cproduct(tc_list) -> List.iter check_type tc_list
  | Catom(c) ->
      let c = crepr c in
      List.iter (occur_check c) c.c_inf;      
      List.iter (occur_check c) c.c_sup
  | Cfun(tc_arg, tc_res) -> check_type tc_arg; check_type tc_res
    
(** order < between types *)
let rec less left_tc right_tc =
  match left_tc, right_tc with
  | Cproduct(l1), Cproduct(l2) -> List.iter2 less l1 l2
  | Catom(c1), Catom(c2) -> less_c c1 c2
  | Cfun(tc_arg1, tc_res1), Cfun(tc_arg2, tc_res2) ->
     less tc_res1 tc_res2; less tc_arg2 tc_arg1 
  | _ -> assert false
                
and less_c left_c right_c =
  let left_c = crepr left_c in
  let right_c = crepr right_c in
  match left_c.c_desc, right_c.c_desc with
  | Cvar, Cvar ->
     occur_check left_c right_c;
     (* [left_c < .... set ...] with [left_c not in set] *)
     (* Now [left_c < ... set + { right_c } *)
     right_c.c_inf <- add left_c right_c.c_inf;
     left_c.c_sup <- add right_c left_c.c_sup     
  | _ -> assert false

let intro_less_c right_c =
  let left_c = new_var () in less_c left_c right_c; left_c
  
(* does it exist a strict path from [c1] to [c2]? *)
let rec strict_path c1 c2 = List.exists (fun c1 -> path c1 c2) (sups c1) 
and path c1 c2 = (equal c1 c2) || (strict_path c1 c2)

 
(* Copy of a causality type *)
let rec fresh tc =
  match tc with
  | Cfun(tc1, tc2) -> Cfun(fresh tc1, fresh tc2)
  | Cproduct(l) -> Cproduct(List.map fresh l)
  | Catom(c) -> Catom(new_var_with_info c)

let rec fresh_on_c c tc =
  match tc with
  | Cfun(tc1, tc2) ->
      let c_left = new_var () in
      less_c c_left c;
      Cfun(fresh_on_c c_left tc1, fresh_on_c c tc2)
  | Cproduct(l) -> Cproduct(List.map (fresh_on_c c) l)
  | Catom _ -> Catom(c)

(* Compute the sup of two causality types *)
let rec suptype is_right left_tc right_tc =
  match left_tc, right_tc with
  | Cproduct(l1), Cproduct(l2) ->
    let tc_list =
      try List.map2 (suptype is_right) l1 l2
      with Invalid_argument _ -> assert false in
    Cproduct(tc_list)
  | Catom(c1), Catom(c2) -> Catom(sup_c is_right c1 c2)
  | Cfun(left_tc1, left_tc2), Cfun(right_tc1, right_tc2) ->
    Cfun(suptype (not is_right) left_tc1 right_tc1,
         suptype is_right left_tc2 right_tc2)
  | _ -> assert false

and sup_c is_right left_c right_c =
    let left_c = crepr left_c in
    let right_c = crepr right_c in
    let c = new_var () in
    if is_right then
      begin less_c left_c c; less_c right_c c end
    else
      begin less_c c left_c; less_c c right_c end;
    c
  
let suptype_list is_right tc_list = 
  match tc_list with
  | [] -> assert false
  | hd :: tl -> List.fold_left (suptype is_right) hd tl
                  
(** Computing a causality type from a type *)
let rec skeleton ty =
  match ty.t_desc with
  | Tvar -> atom (new_var ())
  | Tproduct(ty_list) -> product (List.map skeleton ty_list)
  | Tfun(_, _, ty_arg, ty) ->
     funtype (skeleton ty_arg) (skeleton ty)
  | Tconstr(_, _, _) | Tvec _ -> atom (new_var ())
  | Tlink(ty) -> skeleton ty

(* the type is synchronised on [c] *)
let skeleton_on_c c ty =
  let rec skeleton_on_c is_right c_right ty =
    match ty.t_desc with
    | Tvar | Tconstr(_, _, _) | Tvec _ -> atom c_right
    | Tproduct(ty_list) ->
        product (List.map (skeleton_on_c is_right c_right) ty_list)
    | Tfun(_, _, ty_arg, ty) ->
        let c_left = new_var () in
        (* if is_right then *) less_c c_left c_right;
        funtype
          (skeleton_on_c (not is_right) c_left ty_arg)
          (skeleton_on_c is_right c_right ty)
    | Tlink(ty) -> skeleton_on_c is_right c_right ty in
  skeleton_on_c true c ty

(* the skeleton for the type of a variable. no constraint for function types *)
(* only for other types *)
let skeleton_for_variables ty =
  let c = new_var () in
  let rec skeleton_rec ty =
    match ty.t_desc with
    | Tvar | Tconstr(_, _, _) | Tvec _ -> atom c
    | Tproduct(ty_list) -> product (List.map skeleton_rec ty_list)
    | Tfun _ -> skeleton ty
    | Tlink(ty) -> skeleton_rec ty in
  skeleton_rec ty

(* Returns a causality type that is structurally like [tc] but *)
(* also depend on variables in [cset] *)
let rec on_c is_right cset tc =
  match tc with
  | Cproduct(l) -> Cproduct(List.map (on_c is_right cset) l)
  | Cfun(tc1, tc2) ->
      Cfun(on_c (not is_right) cset tc1, on_c is_right cset tc2)
  | Catom(left_c) ->
      let right_c = new_var () in
      let cset = S.add left_c cset in
      if is_right then S.iter (fun c -> less_c c right_c) cset
      else S.iter (fun c -> less_c right_c c) cset;
      Catom(right_c)

let on_c tc c = on_c true (S.singleton c) tc
    
(** Simplification of types *)
(* Mark useful variables *)
let rec mark tc =
  match tc with
  | Cfun(tc1, tc2) ->
     mark tc1; mark tc2
  | Cproduct(tc_list) -> List.iter mark tc_list
  | Catom(c) -> mark_c c

and mark_c c =
  let c = crepr c in
  match c.c_desc with
  | Cvar -> 
     c.c_useful <- true;
  | Clink(link) -> mark_c link

let mark_and_polarity is_right tc = mark tc; polarity is_right tc
    
(* we compute IO sets [see Pouzet and Raymond, EMSOFT'09] *)
(* IO(c) = { i / i in I /\ i <_O c } and i <_O c iff O(c) subset O(i) *)
(* Partition according to IO, i.e., two variables with the same IO *)
(* get the same representative *)

let is_an_output c =
  c.c_useful && ((c.c_polarity = Pplus) || (c.c_polarity = Pplusminus))
                  
(* compute the set of inputs and outputs *)
let rec ins_and_outs c (inputs, outputs) =
  match c.c_desc with
  | Clink(link) -> ins_and_outs link (inputs, outputs)
  | Cvar ->
     match c.c_polarity with
     | Pplus -> inputs, S.add c outputs
     | Pminus -> S.add c inputs, outputs
     | Pplusminus -> S.add c inputs, S.add c outputs
     | _ -> inputs, outputs
    
let ins_and_outs c_set = S.fold ins_and_outs c_set (S.empty, S.empty)
    
let rec ins_and_outs_of_a_type is_right (inputs, outputs) tc =
  match tc with
  | Cfun(tc1, tc2) ->
     let inputs, outputs =
       ins_and_outs_of_a_type (not is_right) (inputs, outputs) tc1 in
     ins_and_outs_of_a_type is_right (inputs, outputs) tc2
  | Cproduct(tc_list) ->
      List.fold_left
        (ins_and_outs_of_a_type  is_right) (inputs, outputs) tc_list
  | Catom(c) ->
      let c = crepr c in
      if is_right then inputs, S.add c outputs else S.add c inputs, outputs

(* build O(c) *)
let rec outrec acc c =
  let c = crepr c in
  match c.c_desc with
  | Clink(link) -> outrec acc link
  | Cvar ->
     let acc = if is_an_output c then S.add c acc else acc in
     List.fold_left outrec acc c.c_sup

let out c = outrec S.empty c  
let outset cset = S.fold (fun c acc -> outrec acc c) cset S.empty
		      
(* compute io(c) *)
(* io(c) = {i in I / O(c) subseteq O(i) } *)
let rec io inputs o_table c =
  let o = M.find c o_table in
  S.fold
    (fun i' acc ->
       let o' = M.find i' o_table in
       if S.subset o o' then S.add i' acc else acc)
    inputs S.empty
  
(* build a table [c -> O(c)] *)
let build_o_table c_set o_table =
  S.fold (fun i acc -> M.add i (out i) acc) c_set o_table    

(* build a table [c -> IO(c)] *)
let build_io_table inputs o_table c_set io_table =
  S.fold (fun i acc -> M.add i (io inputs o_table i) acc) c_set io_table

(* build a ki table [io -> c] with a unique variable per io set *)
(* and for every [c] the set of greater elements *)
let build_ki_table io_table =
  let ki_table =
    M.fold
      (fun i io acc ->
       if K.mem io acc then acc
       else K.add io (new_gen_var ()) acc)
      io_table K.empty in
  (* then add relation between them according to io. *)
  (* if ki(io1) = c1 and ki(io2) = c2, c1 < c2 iff (io(c1) subset io(c2)) *)
  let dep =
    K.fold
    (fun io_i ki_i acc ->
       K.fold
         (fun io_j ki_j acc ->
            let c = S.compare io_i io_j in
            if c = 0 then acc
            else
	      if S.subset io_i io_j then
		try
		  let c_set = M.find ki_i acc in
		  M.add ki_i (S.add ki_j c_set) acc
		with Not_found -> M.add ki_i (S.singleton ki_j) acc
	      else acc)
	 ki_table acc)
    ki_table M.empty in
  ki_table, dep

(* Given a dependence relation [ai < ai1,..., ain] *)
(* keep only dependences [a-k < b+k'] *)
let filter dep =
  (* only keep a dependence a-k < b+k' *)
  let keep c_left c_right =
    let c_left = crepr c_left in
    let c_right = crepr c_right in
    match c_left.c_polarity, c_right.c_polarity with
    | (Pminus | Pplusminus), (Pplus | Pplusminus) -> true | _ -> false in
  M.fold
    (fun c_left c_set acc -> M.add c_left (S.filter (keep c_left) c_set) acc)
    dep M.empty

(* simplifies a causality type *)
let simplify_by_io tc =
  let inputs, outputs =
    ins_and_outs_of_a_type true (S.empty, S.empty) tc in
  let inputs_outputs = S.union inputs outputs in
  
  (* build the association table [i, O(i)] for every i in I and O *)
  let o_table = build_o_table inputs_outputs M.empty in

  (* then the table of io for every input/output *)
  let io_table = build_io_table inputs o_table inputs_outputs M.empty in

  (* the ki table associates a unique variable per io set *)
  let ki_table, dep = build_ki_table io_table in 
  
  (* computes a type where every variable is replaced by its ki *)
  let rec copy tc =
    match tc with
    | Cfun(tc1, tc2) -> Cfun(copy tc1, copy tc2)
    | Cproduct(tc_list) -> Cproduct(List.map copy tc_list)
    | Catom(c) -> Catom(K.find (M.find c io_table) ki_table) in

  let tc = copy tc in
  (* computes polarities *)
  polarity true tc;
  (* final clean: only keep dependences [a-k < b+k'] *)
  let dep = filter dep in
  
  (* physically apply the dependences *)
  M.iter
    (fun c_left c_set ->
     S.iter (fun c_right -> less_c c_left c_right) c_set) dep;
  tc

   
(* An other simplification method *)
(* Garbage collection: only keep dependences of the form a- < b+ *)
(* this step is done after having called the function mark *)
let rec shorten ty =
  match ty with
  | Cfun(tc1, tc2) -> shorten tc1; shorten tc2
  | Cproduct(tc_list) -> List.iter shorten tc_list
  | Catom(c) -> shorten_c c

and shorten_c c =
  let c = crepr c in
  match c.c_desc with
  | Clink(c) -> shorten_c c
  | Cvar ->
     c.c_visited <- 0;
     (* only keep a dependence a- < b+ *)
     let inf, sup =
       match c.c_polarity with
       | Punknown -> assert false
       | Pplus -> remove_polarity Pplus (short_list false [] c.c_inf), []
       | Pminus -> [], remove_polarity Pminus (short_list true [] c.c_sup)
       | Pplusminus ->
         short_list false [] c.c_inf, short_list true [] c.c_sup in
     c.c_inf <- inf;
     c.c_sup <- sup;
     c.c_visited <- 1       
                      
and short_list is_right acc c_list =
  List.fold_left (short is_right) acc c_list

(* only keep a dependence a- < b+ *)
and remove_polarity p c_list =
  let clear acc c_right =
    match p, c_right.c_polarity with
    | (Pplus, Pplus) | (Pminus, Pminus) -> acc
    | _ -> c_right :: acc in
  List.fold_left clear [] c_list
    
and short is_right acc c =
  match c.c_desc with
  | Clink(c) -> short is_right acc c
  | Cvar ->
      match c.c_visited with
      | -1 -> (* never visited *)
          c.c_visited <- 0;
          let acc =
            short_list is_right acc (if is_right then c.c_sup else c.c_inf) in
          let acc = if c.c_useful then add c acc else acc in
          c.c_visited <- -1;
          acc
      | 0 -> (* currently visited *)
          acc
      | _ -> (* visited in a previous pass *) 
          (* the variable is added only if it is useful *)
          if c.c_useful then add c acc else union c.c_inf acc  

                              
(* Final simplification. *)
(*- if a- has a single sup. b+, it can be replaced by it
 *- if a+ has a single inf. b-, it can be replaced by it. *)
let rec simplify right tc =
  match tc with
  | Cfun(tc1, tc2) -> funtype (simplify (not right) tc1) (simplify right tc2)
  | Cproduct(tc_list) -> product(List.map (simplify right) tc_list)
  | Catom(c) -> Catom(csimplify right c)

and csimplify right c =
  let c = crepr c in
  match c.c_desc with
  | Clink _ -> c
  | Cvar ->
    if right then
      match c.c_inf, c.c_polarity with
      | [c_inf], Pplus ->
          increase_polarity Pplus c_inf;
          c.c_useful <- false; c_inf
      | _ -> c
    else
      match c.c_sup, c.c_polarity with
      | [c_sup], Pminus ->
          increase_polarity Pminus c_sup; 
          c.c_useful <- false; c_sup
      | _ -> c

let simplify is_right tc =
  shorten tc;
  let tc = simplify is_right tc in
  mark_and_polarity is_right tc;
  shorten tc;
  tc

(* Shrink a cycle by keeping only names in [cset] *)
let shrink_cycle cset c_list =
  let shrink c = S.mem c cset in
  List.filter shrink c_list

(* Keep explicit names in a causality cycle *)
let keep_names_in_cycle c_set c_list =
  let keep_name c =
    let c = crepr c in
    match c.c_info with
    | None -> false | Some(info) -> true in
  let keep_var c = S.mem c c_set in
  let c_filtered_list = List.filter keep_name c_list in
  match c_filtered_list with
  | [] -> List.filter keep_var c_list
  | _ -> c_filtered_list

(* Compute the transitive reduction of the dependence relation *)
let reduce cset =
  (* build the graph *)
  let c_to_i, g, _ =
    S.fold (fun c (c_to_i, g, i) -> M.add c i c_to_i, Graph.add i c g, i+1)
      cset (M.empty, Graph.empty, 0) in 
  (* Format.printf "%a" (Graph.print Pcaus.caus) g; *)
  let g =
    S.fold
    (fun c g ->
       let i = M.find c c_to_i in
       let sups =
         List.fold_left
           (fun acc c -> Graph.S.add (M.find c c_to_i) acc)
           Graph.S.empty c.c_sup in
       Graph.add_before (Graph.S.singleton i) sups g) cset g in
  let g = Graph.outputs g in
  (* compute the transitive reduction *)
  (* Format.printf "%a" (Graph.print Pcaus.caus) g; *)
  let g = Graph.transitive_reduction g in
  (* Format.printf "%a" (Graph.print Pcaus.caus) g; *)
  (* reconstruct the relation *)
  S.iter
    (fun c ->
       let i = M.find c c_to_i in
       let sups =
         Graph.S.fold (fun j acc -> (Graph.containt j g) :: acc)
           (Graph.successors i g) [] in
       c.c_sup <- sups)
    cset
 
    
(** Computes the dependence relation from a list of causality variables *)
(* variables in [already] are disgarded *)
let relation (already, rel) cset =
  let rec relation (already, rel) c =
    let c = crepr c in
    if S.mem c already then already, rel
    else if c.c_sup = [] then already, rel
    else List.fold_left
        relation (S.add c already, (c, set c.c_sup) :: rel) c.c_sup in
  S.fold (fun c acc -> relation acc c) cset (already, [])

(** Generalisation of a type *)
(* the level of generalised type variables *)
(* is set to [generic]. Returns [generic] when a sub-term can be generalised *)
let list_of_vars = ref []

let rec gen tc =
  match tc with
  | Cproduct(tc_list) -> List.iter gen tc_list
  | Cfun(tc1, tc2) -> gen tc1; gen tc2
  | Catom(c) -> ignore (cgen c)

and cgen c =
  let c = crepr c in
  match c.c_desc with
  | Cvar ->
      c.c_useful <- false;
      if c.c_level > !binding_level
      then 
        begin
          c.c_level <- generic;
          let level = gen_set c.c_sup in
          c.c_level <- level;
          if level = generic then list_of_vars := c :: !list_of_vars
        end;
      c.c_level
  | Clink(link) -> cgen link
                     
and gen_set l = List.fold_left (fun acc c -> max (cgen c) acc) generic l
    
(** Main generalisation function *)
let generalise tc =
  list_of_vars := [];
  (* we compute useful variables *)
  mark_and_polarity true tc;
  (* type simplification *)
  (* let tc = simplify true tc in *)
  let tc =
    if !Misc.no_simplify_causality_type then tc else simplify_by_io tc in
  (* check_type tc; *)
  gen tc;
  let c_set = vars S.empty tc in
  if not !Misc.no_simplify_causality_type then reduce c_set;
  let _, rel = relation (S.empty, []) c_set in
  { typ_vars = !list_of_vars; typ_rel = rel; typ = tc }

(** Instantiation of a type *)
(* save and cleanup links *)
let links = ref []
    
let save link = links := link :: !links
let cleanup () = List.iter (fun c -> c.c_desc <- Cvar) !links; links := []

(* makes a copy of the type scheme *)
let rec copy tc ty = 
  let rec ccopy c =
    match c.c_desc with
    | Cvar ->
       if c.c_level = generic
       then
         let sup_list = List.map ccopy c.c_sup in
         let v = { (new_var ()) with c_sup = sup_list } in
         c.c_desc <- Clink(v);
         save c;
         v
       else c
    | Clink(link) -> if c.c_level = generic then link else ccopy link in

  let { t_desc = t_desc } as ty = Types.typ_repr ty in
  match tc, t_desc with
  | Cfun(tc1, tc2), Tfun(_, _, ty1, ty2) ->
     funtype (copy tc1 ty1) (copy tc2 ty2)
  | Cproduct(tc_list), Tproduct(ty_list) ->
     begin try product (List.map2 copy tc_list ty_list)
           with | Invalid_argument _ -> assert false end
  | Catom(c), _ -> skeleton_on_c (ccopy c) ty
  | _ -> assert false

(* makes a copy of the type scheme *)
let rec copy tc = 
  let rec ccopy c =
    match c.c_desc with
    | Cvar ->
       if c.c_level = generic
       then
         let sup_list = List.map ccopy c.c_sup in
         let v = { (new_var ()) with c_sup = sup_list } in
         c.c_desc <- Clink(v);
         save c;
         v
       else c
    | Clink(link) -> if c.c_level = generic then link else ccopy link in

  match tc with
  | Cfun(tc1, tc2) -> funtype (copy tc1) (copy tc2)
  | Cproduct(tc_list) -> product (List.map copy tc_list)
  | Catom(c) -> atom (ccopy c)

(* instanciate the causality type according to the type *)
let rec instance tc ty = 
  let { t_desc = t_desc } as ty = Types.typ_repr ty in
  match tc, t_desc with
  | Cfun(tc1, tc2), Tfun(_, _, ty1, ty2) ->
     funtype (instance tc1 ty1) (instance tc2 ty2)
  | Cproduct(tc_list), Tproduct(ty_list) ->
     begin try product (List.map2 instance tc_list ty_list)
           with | Invalid_argument _ -> assert false end
  | Catom(c), _ -> skeleton_on_c c ty
  | _ -> assert false

(* subtyping *)
let rec subtype right tc =
  match tc with
  | Cfun(tc1, tc2) ->
      funtype (subtype (not right) tc1) (subtype right tc2)
  | Cproduct(tc_list) ->
      begin try product (List.map (subtype right) tc_list)
        with | Invalid_argument _ -> assert false end
  | Catom(c) ->
      let new_c = new_var () in
      if right then less_c c new_c else less_c new_c c;
      atom new_c
        
let instance { typ = tc } ty =
  let tc = copy tc in
  cleanup ();
  let tc = subtype true tc in
  instance tc ty

(** Type instance *)
let instance { value_caus = tcs_opt } ty =
  (* build a default signature *)
  let default ty =
    let c = new_var () in
    skeleton_on_c c ty in
  match tcs_opt with
    | None -> 
       (* if no causality signature is declared, a default one is built *)
       (* from the type signature *)
       subtype true (default ty)
    | Some(tcs) -> instance tcs ty

(* check that [tc] is of the form [tc1;...;tc_arity] *)
let filter_product arity tc =
  match tc with
    | Cproduct(l) when List.length l = arity -> l
    | _ -> assert false

(* check that [tc] is a function type *)
let filter_arrow tc =
  match tc with
  | Cfun(tc1, tc2) -> tc1, tc2
  | _ -> assert false

(* Environment for causality types *)
type tentry = 
  { t_typ: tc;      (* the causality type of x *)
    t_last_typ: tc option; (* [last x] is allowed *)
  }

(* simplifies a typing environment *)
let simplify_by_io_env env expected_tc actual_tc =
  let mark_env _ { t_typ = tc; t_last_typ = ltc_opt } =
    mark_and_polarity true tc;
    Misc.optional_unit mark_and_polarity true ltc_opt in
  let simplify_env { t_typ = tc; t_last_typ = ltc_opt } =
    let tc = simplify_by_io tc in
    let ltc_opt = Misc.optional_map simplify_by_io ltc_opt in
    { t_typ = tc; t_last_typ = ltc_opt } in
  Env.iter mark_env env;
  mark_and_polarity true expected_tc;
  mark_and_polarity true actual_tc;
  let env = Env.map simplify_env env in
  (* Computes the set of free variables and dependence relations *)
  let cset =
    Env.fold
      (fun _ { t_typ = tc; t_last_typ = ltc_opt } acc ->
         Misc.optional vars (vars acc tc) ltc_opt) env S.empty in
  let cset = vars (vars cset expected_tc) actual_tc in
  let already, rel = relation (S.empty, []) cset in
  env, cset, rel, simplify_by_io expected_tc, simplify_by_io actual_tc

(* compute the dependence relations *)
let prel ff rel =
  match rel with
  | [] -> ()
  | _ -> Format.fprintf ff "@[<hov2>@ with@ @[%a@]@]" Pcaus.relation rel
           
(* prints the typing environment *)
let penv ff env =
  (* print every entry in the typing environment *)
  let pentry ff (n, { t_typ = tc; t_last_typ = ltc_opt }) =
    match ltc_opt with
    | None -> Format.fprintf ff "@[%a: %a@]" Printer.source_name n Pcaus.ptype tc
    | Some(ltc) ->
        Format.fprintf ff "@[%a: %a | %a@]"
          Printer.source_name n Pcaus.ptype tc Pcaus.ptype ltc in
  let env = Env.bindings env in
  Pp_tools.print_list_r pentry "{" ";" "}" ff env
