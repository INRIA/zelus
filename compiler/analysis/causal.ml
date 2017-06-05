(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2017                                               *)
(*                                                                        *)
(*  Timothy Bourke          Marc Pouzet                                   *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
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
       
(** and a module to represent the successors of a causality variable *)
module M = struct
  include (Map.Make(Defcaus))
  let fprint_t fprint_v ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun k v -> Format.fprintf ff "%a->%a@ " Pcaus.caus k fprint_v v) s;
    Format.fprintf ff "}@]"
end

let fprint_t = S.fprint_t
let fprint_tt = M.fprint_t S.fprint_t
                           
  

let set c_list = List.fold_left (fun acc c -> S.add c acc) S.empty c_list
  
type error =
  | ClashTypes of tc * tc * cycle
  | ClashLast of Ident.t
	      
and cycle = Defcaus.t list

(* typing errors *)
exception Unify of cycle
exception Error of error
				       
let new_var () = 
  { c_desc = Cvar; c_index = symbol#name; c_level = !binding_level;
    c_sup = []; c_useful = false; 
    c_polarity = Punknown; c_info = None }
let new_var_with_info { c_info = i } = { (new_var ()) with c_info = i }
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

(* equality of two nodes *)
let equal c1 c2 =
  let c1 = crepr c1 in
  let c2 = crepr c2 in
  c1.c_index = c2.c_index

let rec add c l = 
  match l with 
    | [] -> [c] 
    | c1 :: l1 -> if equal c c1 then l else c1 :: (add c l1)

let rec union l1 l2 = 
  let rec mem c l =
    match l with | [] -> false | c1 :: l -> (equal c c1) || (mem c l) in
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | c :: l1, l2 ->
     if mem c l2 then union l1 l2 else c :: union l1 l2

let set l = List.fold_left (fun acc c -> add c acc) [] l
		      
(* sups *)
let sups c = let c = crepr c in c.c_sup
		 
let rec annotate n = function
  | Catom(c) -> atom(cannotate n c)
  | Cproduct(ty_list) -> product(List.map (annotate n) ty_list)
  | Cfun _ as ty -> ty
and cannotate n c =
  let c = crepr c in
  c.c_info <- Some(n); c

(* The set of variables of a causality type *)
let rec vars acc = function
  | Catom(c) -> S.add (crepr c) acc
  | Cproduct(ty_list) -> List.fold_left vars acc ty_list
  | Cfun(ty_arg, ty_res) -> vars (vars acc ty_arg) ty_res
			 
(** Sets the polarity of a type. *)
let cpolarity pol c =
  match pol, c.c_polarity with
    | _, Punknown -> c.c_polarity <- if pol then Pplus else Pminus
    | (true, Pplus) | (false, Pminus) -> ()
    | _ -> c.c_polarity <- Pplusminus

(** check for cycles. Does [index] appears in the set of elements *)
(* greater than [c]? *)
let rec occur_check level index c =
  let rec check path c =
    match c.c_desc with
      | Cvar -> 
	  if c.c_level > level then c.c_level <- level;
	  if c.c_index = index 
	  then raise (Unify (List.rev path))
	  else List.iter (check (c :: path)) c.c_sup
      | Clink(link) -> check path link
  in check [c] c

(** Unification *)
let rec unify cunify left_tc right_tc =
  match left_tc, right_tc with
  | Cproduct(l1), Cproduct(l2) -> List.iter2 (unify cunify) l1 l2
  | Catom(c1), Catom(c2) -> cunify c1 c2
  | Cfun(tc_arg1, tc_res1), Cfun(tc_arg2, tc_res2) ->
     unify cunify tc_res1 tc_res2; unify cunify tc_arg2 tc_arg1 
  | _ -> assert false
                
let rec cunify left_c right_c =
  if left_c == right_c then ()
  else 
    let left_c = crepr left_c in
    let right_c = crepr right_c in
    if left_c == right_c then ()
    else
      match left_c.c_desc, right_c.c_desc with
      | Cvar, Cvar ->
         List.iter (occur_check left_c.c_level left_c.c_index) right_c.c_sup;
	 List.iter (occur_check right_c.c_level right_c.c_index) left_c.c_sup;
	 left_c.c_desc <- Clink(right_c);
	 right_c.c_sup <- union left_c.c_sup right_c.c_sup
      | _ -> assert false
                    
let rec cless left_c right_c =
  let left_c = crepr left_c in
  let right_c = crepr right_c in
  match left_c.c_desc, right_c.c_desc with
  | Cvar, Cvar ->
     occur_check left_c.c_level left_c.c_index right_c;
     (* [left_c < .... set ...] with [left_c not in set] *)
     (* Now [left_c < ... set + { right_c } *)
     left_c.c_sup <- add right_c left_c.c_sup
  | _ -> assert false
                
(* does it exist a strict path from [c1] to [c2]? *)
let rec strict_path c1 c2 = List.exists (fun c1 -> path c1 c2) (sups c1) 
and path c1 c2 = (equal c1 c2) || (strict_path c1 c2)
                                    
(* the main entry functions for comparing causality types *)
let type_before_type left_tc right_tc =
  try
    unify cless left_tc right_tc
  with Unify(cycle) -> raise (Error (ClashTypes(left_tc, right_tc, cycle)))

let ctype_before_ctype left_c right_c =
  try
    cless left_c right_c
  with Unify(cycle) ->
    raise (Error (ClashTypes(atom left_c, atom right_c, cycle)))

let cunify_types left_c right_c =
  try
    cunify left_c right_c
  with Unify(cycle) ->
    raise (Error(ClashTypes(atom left_c, atom right_c, cycle)))

(* Copy of a causality type *)
let rec fresh tc =
  match tc with
  | Cfun(tc1, tc2) -> Cfun(fresh tc1, fresh tc2)
  | Cproduct(l) -> Cproduct(List.map fresh l)
  | Catom(c) -> Catom(new_var_with_info c)
		     
(* Returns a causality type that is structurally like [tc] but *)
(* depends on both [tc] and [cset] *)
let rec supcset cset tc =
  match tc with
    | Cproduct(l) -> Cproduct(List.map (supcset cset) l)
    | Cfun(tc1, tc2) -> Cfun(tc1, supcset cset tc2)
    | Catom(left_c) ->
       let right_c = new_var () in
       S.iter (fun c -> ctype_before_ctype c right_c) (S.add left_c cset);
       Catom(right_c)

let rec supc c tc = supcset (S.singleton c) tc

(* Compute the sup of two causality types *)
let rec sup left_tc right_tc =
  let rec supc left_c right_c =
    let left_c = crepr left_c in
    let right_c = crepr right_c in
    let c = new_var () in
    ctype_before_ctype left_c c; ctype_before_ctype right_c c;
    c in
  match left_tc, right_tc with
  | Cproduct(l1), Cproduct(l2) when List.length l1 = List.length l2 -> 
     Cproduct(List.map2 sup l1 l2)
  | Catom(c1), Catom(c2) -> Catom(supc c1 c2)
  | Cfun(left_tc1, left_tc2), Cfun(right_tc1, right_tc2) ->
     Cfun(sup left_tc1 right_tc1, sup left_tc2 right_tc2)
  | _ -> assert false

let sup_list tc_list = 
  match tc_list with
  | [] -> assert false
  | hd :: tl -> List.fold_left sup hd tl

		     
(** Synchronise a type *)
let synchronise left_c tc =
  let rec csynchronise  right_c =
    let right_c = crepr right_c in
    match right_c.c_desc with
    | Cvar -> cunify_types left_c right_c
    | Clink(link) -> csynchronise link
  and synchronise tc =
    match tc with
    | Cproduct(tc_list) -> List.iter synchronise tc_list
    | Cfun(tc1, tc2) -> synchronise tc1; synchronise tc2
    | Catom(right_c) -> csynchronise right_c in
  synchronise tc

(** Computing a causality type from a type *)
let rec skeleton ty =
  match ty.t_desc with
  | Tvar -> atom (new_var ())
  | Tproduct(ty_list) -> product (List.map skeleton ty_list)
  | Tfun(_, _, ty_arg, ty) ->
     funtype (skeleton ty_arg) (skeleton ty)
  | Tconstr(_, _, _) | Tvec _ -> atom (new_var ())
  | Tlink(ty) -> skeleton ty

let rec skeleton_on_c c ty =
  match ty.t_desc with
    | Tvar -> atom c
    | Tproduct(ty_list) -> product (List.map (skeleton_on_c c) ty_list)
    | Tfun(_, _, ty_arg, ty) ->
       let c_left = new_var () in
       cless c_left c;
       funtype (skeleton_on_c c_left ty_arg) (skeleton_on_c c ty)
    | Tconstr(_, _, _) | Tvec _ -> atom c
    | Tlink(ty) -> skeleton_on_c c ty

(** Simplification of types *)
(* Mark useful/useless variables and returns them *)
let rec mark right acc tc =
  match tc with
  | Cfun(tc1, tc2) ->
     let acc = mark (not right) acc tc1 in
     mark right acc tc2
  | Cproduct(tc_list) -> List.fold_left (mark right) acc tc_list
  | Catom(c) -> cmark right acc c

and cmark right acc c =
  let c = crepr c in
  match c.c_desc with
  | Cvar -> 
     c.c_useful <- true;
     cpolarity right c;
     S.add c acc
  | Clink(link) -> cmark right acc link
  			
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
		      
(* build O(c) *)
let rec out c =
  let rec outrec acc c =
    let c = crepr c in
    match c.c_desc with
    | Clink(link) -> outrec acc link
    | Cvar ->
       let acc = if is_an_output c then S.add c acc else acc in
       List.fold_left outrec acc c.c_sup in
  outrec S.empty c  

(* simplifies a set of causalities *)
let simplify c_set =
  (* is-it an output? *)
  let inputs, outputs = S.fold ins_and_outs c_set (S.empty, S.empty) in
  let inputs_outputs = S.union inputs outputs in

  (* build the association table [i, O(i)] for every i in I and O *)
  let o_table =
    S.fold (fun i acc -> M.add i (out i) acc) inputs M.empty in
  let o_table =
    S.fold (fun i acc -> M.add i (out i) acc) outputs o_table in
    
  (* compute io(c) *)
  (* io(c) = {i in I / O(c) subseteq O(i) } *)
  let rec io c =
    let o = M.find c o_table in
    S.fold
      (fun i' acc ->
       let o' = M.find i' o_table in
       if S.subset o o' then S.add i' acc else acc)
      inputs S.empty in
  
  (* then the table of io for every input/output *)
  let io_table = S.fold (fun i acc -> M.add i (io i) acc) inputs M.empty in
  let io_table = S.fold (fun o acc -> M.add o (io o) acc) outputs io_table in

  (* finally, the dependence relation is that of [io], i.e., *)
  (* c1 < c2 iff io(c1) subset io(c2) *)
  (* moreover, variables are partitioned according to [io], i.e., *)
  (* [c1 eq c2 iff io(c1) = io(c2)] *)
  let set left_c right_c = cunify_types left_c right_c in
  let less left_c right_c = ctype_before_ctype left_c right_c in
  S.iter (fun c -> (crepr c).c_sup <- []) inputs_outputs;
  S.iter
    (fun i -> 
      let io_of_i = M.find i io_table in
      S.iter 
	(fun o ->
	  let io_of_o = M.find o io_table in
	  if not (equal i o)
	  then
            if S.equal io_of_i io_of_o then set i o
            else if S.subset io_of_i io_of_o then less i o
            else if S.subset io_of_o io_of_i then less o i)
	outputs)
    inputs    
    
(* Eliminate doublons, e.g., [c < b, b] and dependences to variables *)
(* which are not input or outputs *)
(* used only when a type error occurs. *)
let useless c_set =
  let rec remove_useless_variables c_set = S.iter remove_useless c_set 
  and remove_useless c = 
    let c = crepr c in
    c.c_sup <- useful_list [] c.c_sup
  and useful_list acc l = List.fold_left useful acc l
  and useful acc c_right =
    let c_right = crepr c_right in
    match c_right.c_desc with
    | Cvar -> 
       if c_right.c_useful then add c_right acc
       else useful_list acc c_right.c_sup
    | Clink(link) -> useful acc link in
  remove_useless_variables c_set

(* Shrink a cycle by keeping only names in [cset] *)
let shrink_cycle cset c_list =
  let shrink c = S.mem c cset in
  List.filter shrink c_list
	      
(** Computes the dependence relation from a list of causality variables *)
(* variables in [already] are disgarded *)
let relation cset =
  let rec relation (already, rel) c =
    let c = crepr c in
    if S.mem c already then already, rel
    else if c.c_sup = [] then already, rel
    else List.fold_left
           relation (S.add c already, (c, set c.c_sup) :: rel) c.c_sup in
  let _, rel = S.fold (fun c acc -> relation acc c) cset (S.empty, []) in
  rel

(** Generalisation of a type *)
(* the level of generalised type variables *)
(* is set to [generic]. Returns [generic] when a sub-term *)
(* can be generalised *)

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
  let c_set = mark true S.empty tc in
  (* type simplification *)
  (* useless c_set; *) simplify c_set;
  ignore (gen tc);
  let rel = relation c_set in
  { typ_vars = !list_of_vars; typ_rel = rel; typ = tc }

(** Instantiation of a type *)
(* save and cleanup links *)
let links = ref []
    
let save link = links := link :: !links
let cleanup () = List.iter (fun c -> c.c_desc <- Cvar) !links; links := []

(* instanciation *)
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

  let { t_desc = tydesc } as ty = Types.typ_repr ty in
  match tc, tydesc with
  | Cfun(tc1, tc2), Tfun(_, _, ty1, ty2) ->
     funtype (copy tc1 ty1) (copy tc2 ty2)
  | Cproduct(tc_list), Tproduct(ty_list) ->
     begin try product (List.map2 copy tc_list ty_list)
           with | _ -> assert false end
  | Catom(c), _ -> skeleton_on_c (ccopy c) ty
  | _ -> assert false


(* subtyping *)
let rec subtype right tc =
  match tc with
  | Cfun(tc1, tc2) ->
     funtype (subtype (not right) tc1) (subtype right tc2)
  | Cproduct(tc_list) ->
     begin try product (List.map (subtype right) tc_list)
           with | _ -> assert false end
  | Catom(c) ->
     let new_c = new_var () in
     if right then cless c new_c else cless new_c c;
     atom new_c

let instance { typ = tc } ty =
  let tc = copy tc ty in
  cleanup ();
  tc

(** Type instance *)
let instance { value_caus = tcs_opt } ty =
  (* build a default signature *)
  let default ty =
    let c = new_var () in
    skeleton_on_c c ty in
  let tc = match tcs_opt with
    | None -> 
       (* if no causality signature is declared, a default one is built *)
       (* from the type signature *)
       default ty
    | Some(tcs) -> instance tcs ty in
  subtype true tc

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
module Cenv =
  struct
    type centry =
	{ mutable last: bool; (* [last x] is allowed *)
	  cur_tc: Defcaus.tc; (* the causality type for [x] *)
	  last_tc: Defcaus.tc; (* the causality type for [last x] *)
	}

    (* Ordering between two environments. This is done structurally *)
    (* [x:tcx' | ltcx'] < [x: tcx | ltcx] iff *)
    (* [tcx' < tcx & ltcx < ltcx' ] *)
    (* only keeps names in [left_env] *)
    let before left_env right_env =
      let before x left_opt right_opt =
	match left_opt, right_opt with
	| None, _ -> None
	| Some(entry), None -> Some(entry)
	| Some { last = l1; cur_tc = tc1; last_tc = ltc1 },
	  Some { last = l2; cur_tc = tc2; last_tc = ltc2 } ->
	   if not l1 && l2 then raise (Error(ClashLast(x)))
	   else
             type_before_type tc1 tc2; type_before_type ltc1 ltc2; left_opt in
      Env.merge before left_env right_env

    (* Computes the sup of two typing environments *)
    let sup left_env right_env =
      let sup x left_opt right_opt =
	match left_opt, right_opt with
	| None, None -> None
	| None, Some(entry) -> Some(entry)
	| Some(entry), None -> Some(entry)
	| Some({ last = l1; cur_tc = tc1; last_tc = ltc1 }), 
	  Some({ last = l2; cur_tc = tc2; last_tc = ltc2 }) -> 
	   Some({ last = l1 && l2; cur_tc = sup tc1 tc2;
                  last_tc = sup ltc1 ltc2 }) in
      Env.merge sup left_env right_env
		
    let suplist env_list = List.fold_left sup Env.empty env_list
					  
    (* Computes the sup between a causality dependence *)
    (* and an environment *)
    let supcset cset env =
      Env.map
	(fun ({ cur_tc = tc } as centry) ->
	 { centry with cur_tc = supcset cset tc })
	env
	
    let supc c env = supcset (S.singleton c) env
		      
    (* Makes an environment for the causality type of [x] and [last x] *)
    (* from a basic environment that containt the causality type of [x] *)
    let make expected_k env =
      (* in a continuous context, [last x = x]. No constraint *)
      (* otherwise *)
      let make tc =
	let is_last =
          match expected_k with | Tdiscrete(true) -> true | _ -> false in
        { last = is_last; cur_tc = tc; last_tc = fresh tc } in
      Env.map make env

    (* All names from [defnames] are associated to fresh copies *)
    (* and can be accessed through last *)
    let last { dv = dv } env =
      let last n ({ cur_tc = tc; last_tc = ltc } as centry) acc =
	if Ident.S.mem n dv then
	  Env.add n { last = false; cur_tc = fresh tc; last_tc = ltc } acc
	else Env.add n centry acc in
      Env.fold last env Env.empty

    (* remove the field [last = true] from entries *)
    let unlast env = Env.map (fun entry -> { entry with last = false }) env
              
    (* Computes the dependence relation for a set of causality types *)
    (* in a typing environment *)
    let mark right acc env =
      let entry n { cur_tc = tc; last_tc = ltc } acc =
	mark right (mark right acc tc) ltc in
      Env.fold entry env acc
		
    (* print the type environment. Only keep names in the dependence *)
    (* relation that are present either in [cset] or variables from *)
    (* the types in this environment *)
    let penv cset ff env =
      (* compute the set of useful variables *)
      let cset = mark true cset env in
      (* remove useless dependences *)
      useless cset;
      (* print every entry in the typing environment *)
      let pentry ff (n, { cur_tc = tc; last_tc = ltc }) =
	Format.fprintf ff "@[%a: %a | %a@]"
		       Printer.source_name n Pcaus.ptype tc Pcaus.ptype ltc in
      (* print the relation *)
      let env = Env.bindings env in
      let rel = relation cset in
      Format.fprintf ff
		     "@[<hov>%a@ with@ @[%a@]@.@]"
		     (Pp_tools.print_list_r pentry "[" ";" "]") env
		     Pcaus.relation rel
  end
