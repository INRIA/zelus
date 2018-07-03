(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2018                                               *)
(*                                                                        *)
(*  Marc Pouzet Timothy Bourke                                            *)
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

(* a module to represent the set of successors of a causality variable *)
module M = struct
  include (Map.Make(Defcaus))
  let fprint_t fprint_v ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun k v -> Format.fprintf ff "%a->%a@ " Pcaus.caus k fprint_v v) s;
    Format.fprintf ff "}@]"
end
  
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
let equal c1 c2 =
  let c1 = crepr c1 in
  let c2 = crepr c2 in
  c1.c_index = c2.c_index

let rec add c l = 
  match l with 
  | [] -> [c] 
  | c1 :: l1 -> if equal c c1 then l else c1 :: (add c l1)

let rec remove c l =
  match l with
  | [] -> []
  | c1 :: l1 -> if equal c c1 then l1 else c1 :: (remove c l1)

let rec union l1 l2 = 
  let rec mem c l =
    match l with | [] -> false | c1 :: l -> (equal c c1) || (mem c l) in
  match l1, l2 with
  | [], l2 -> l2 | l1, [] -> l1
  | c :: l1, l2 -> if mem c l2 then union l1 l2 else c :: union l1 l2

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
  | Catom(c) -> vars_c acc c
  | Cproduct(ty_list) -> List.fold_left vars acc ty_list
  | Cfun(ty_arg, ty_res) -> vars (vars acc ty_arg) ty_res

and vars_c acc c = S.add (crepr c) acc
    
(** Sets the polarity of a type. *)
let polarity_c c right =
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

(** Unification *)
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
  | Cfun(tc1, tc2) -> Cfun(fresh_on_c c tc1, fresh_on_c c tc2)
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

let rec skeleton_on_c c ty =
  match ty.t_desc with
  | Tvar -> atom c
  | Tproduct(ty_list) -> product (List.map (skeleton_on_c c) ty_list)
  | Tfun(_, _, ty_arg, ty) ->
      let c_left = new_var () in
      less_c c_left c;
      funtype (skeleton_on_c c_left ty_arg) (skeleton_on_c c ty)
  | Tconstr(_, _, _) | Tvec _ -> atom c
  | Tlink(ty) -> skeleton_on_c c ty

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
let rec mark right tc =
  match tc with
  | Cfun(tc1, tc2) ->
     mark (not right) tc1; mark right tc2
  | Cproduct(tc_list) -> List.iter (mark right) tc_list
  | Catom(c) -> mark_c right c

and mark_c right c =
  let c = crepr c in
  match c.c_desc with
  | Cvar -> 
     c.c_useful <- true;
     polarity_c c right
  | Clink(link) -> mark_c right link
                        
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
let simplify_by_io tc =
  let c_set = vars S.empty tc in
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
  let set left_c right_c =
    let left_c = crepr left_c in
    match left_c.c_desc with
    | Cvar ->
        right_c.c_sup <- union left_c.c_sup right_c.c_sup;
        right_c.c_inf <- union left_c.c_inf right_c.c_inf;
        left_c.c_desc <- Clink(right_c)
    | _ -> () in
  let less left_c right_c =
    let left_c = crepr left_c in
    match left_c.c_desc with
    | Cvar -> left_c.c_sup <- add right_c left_c.c_sup
    | _ ->  () in

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
        inputs_outputs)
    inputs_outputs;
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
  mark is_right tc;
  shorten tc;
  tc

(* Shrink a cycle by keeping only names in [cset] *)
let shrink_cycle cset c_list =
  let shrink c = S.mem c cset in
  List.filter shrink c_list
  
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
  mark true tc;
  (* type simplification *)
  (* let tc = simplify true tc in *)
  let tc = if !Misc.no_simplify then tc else simplify_by_io tc in
  gen tc;
  let c_set = vars S.empty tc in
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
    mark false tc; Misc.optional_unit mark false ltc_opt in
  let simplify_env { t_typ = tc; t_last_typ = ltc_opt } =
    let tc = simplify_by_io tc in
    let ltc_opt = Misc.optional_map simplify_by_io ltc_opt in
    { t_typ = tc; t_last_typ = ltc_opt } in
  Env.iter mark_env env;
  mark true expected_tc;
  mark true actual_tc;
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
           
(* compute the dependence relations *)
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
