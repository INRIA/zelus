(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2025 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* add extra code for in-place modification of the continuous state vector *)
(* see Ztypes.ml *)

(* A continuous machine of the form                *)
(* machine m s1 ... =                              *)
(*    memories (k_i m_k: t_i)_{i in I}             *)
(*    instance (discrete (j_i: f_i)_{i in J}       *)
(*    instance (continuous (j_i: f'_i)_{i in J'}   *)
(*    method (meth_l p_l = e_l)_{l in L}           *)
(*                                                         *)
(* where s1... are static parameters                       *)
(* is translated into                                      *)
(* machine m s1 ... cstate =                               *)
(*    memories (k_i m_k: t_i)_{i in I}                     *)
(*    instance (discrete (j_i: f_i)_{i in J}               *)
(*    instance (continuous (j_i: f'_i cstate)_{i in J'}    *)
(*    method (meth_l p_l = e_l')_{l in L}                  *)
(*                                                         *)
(* the body of the step method is extended to read/write   *)
(* entries from the following data-structure               *)
(* on the global parameter cstate                          *)
(* type cstate =
 *-  { mutable dvec : float array;
 *-    mutable cvec : float array;
 *-    mutable zinvec : bool array;
 *-    mutable zoutvec : float array;
 *-    mutable cindex : int;
 *-    mutable zindex : int;
 *-    mutable cend : int;
 *-    mutable zend : int;
 *-    mutable cmax : int;
 *-    mutable zmax : int;
 *-    mutable horizon : float;
 *-    mutable major : bool }                           *)

(* The main class takes an extra static argument
 *- suppose that [csize] is the length of the state vector of the current block;
 *- x1:float[size1],..., xn:float[sizen] are the continuous state variables;
 *- m1:zero[size'1],..., mk:zero[size'k] are the zero-crossing variables;
 *- method step(arg1,...,argl) = ...body... is the step method.
 *-
 *- rewrite it into:
 *-
 *- method step(arg1,...,argl) =
 *-    let c_start = cstate.cindex in (* current position of the cvector *)
 *-    var cpos = c_start in
 *-    let z_start = cstate.zindex in (* current position of the zvector *)
 *-    cstate.cindex <- cstate.cindex + csize; 
 *-    cstate.zindex <- cstate.zindex + zsize;
 *-    m <- cstate.major;
 *-    var zpos = z_start in
 *-    if cstate.major then 
 *-        dzero cstate.dvec c_start csize (* set all speeds to 0.0 *)
 *-    else ((* copy the value of the continuous state vector of the solver *)
 *-          (* into the local continuous state variables *)
 *-          cin cstate x1 ci;...; cin xn (ci+size1+...+size(n-1)));
 *-          ... cpos is incremented
 *-    let result = ...body... in
 *-    cpos <- c_start;
 *-    if cstate.major then 
 *-        ((* copy the local continuous state variables into *)
 *-         (* the continuous state vector of the solver *)
 *-         cout cstate x1 ci;...; cout cstate ck (zi+size'1+...+size'(n-1));
 *-        ... cpos is incremented
 *-         (* h is the horizon of the block *)
 *-         cstate.horizon <- min cstate.horizon h 
 *-         (* the zero-crossing variables are set to false *)
 *-         m1 <- false; ...; mk <- false;
 *-         ... zpos is incremented)
 *-    else ((* copy the zero-crossing vector of the solver into the local *)
 *-          (* zero-crossing variables *)
 *-          zin cstate m1 zi;...; zin cstate mk (zi+size'1+...+size'(k-1));
 *-          ... zpos is incremented
 *-          zpos <- z_start;
 *-          (* copy the local zero-crossing variables into the *)
 *-          (* zero-crossing vector of the solver *)
 *-          zout cstate m1 zi;...; zout cstate mk (zi+size'1+...+size'(k-1));
 *-          ... zpos is incremented
 *-          (* copy the local derivatives into the vector of derivative *)
 *-          (* of the solver *)
 *-          dout cstate x1 ci;...; dout cstate ck (zi+size'1+...+size'(n-1));
 *-          ... cpos is incremented);
 *-    result
 *-
 *- Add to the initialization code: 
 *-    cmax csize; 
 *-    zmax zsize
 *- which increments the size of the continuous state and zero-crossing vectors *)

open Misc
open Ident
open Lident
open Deftypes
open Obc
open Oaux
       
let typ_cstate =
  Aux.make (Zelus.Etypeconstr(Modname {qual = "Ztypes"; id = "cstate" }, []))

let varpat id ty = Evarpat { id; ty }
let modname x = Lident.Modname { Lident.qual = "Zls"; Lident.id = x }
let access x label = Erecord_access { arg = local x; label = Name label }

(* [x := !x + 1] *)
let incr_pos x = Eassign(Eleft_name x, Oaux.plus_opt (varmut x) one)
let set x e = Eassign(Eleft_name x, e)

let i = Ident.fresh "i"

(* cstate.horizon <- min cstate.horizon h *)
let set_horizon cstate h =
  Eassign(Eleft_record_access
            { arg = Eleft_name(cstate); label = Name "horizon" },
          min (access cstate "horizon") (Estate(Eleft_state_name h)))

(* m <- cstate.major *)
let set_major cstate m =
  Eassign_state(Eleft_state_name(m), access cstate "major")

let set_time cstate m =
  Eassign_state(Eleft_state_name(m), access cstate "time")

(* [cstate.field <- cstate.field + i] *)
let incr cstate field ie =
  Eassign(Eleft_record_access { arg = Eleft_name cstate; label = Name(field) },
          Oaux.plus_opt (access cstate field) ie)
             
let cmax cstate ie = incr cstate "cmax" ie
let zmax cstate ie = incr cstate "zmax" ie
let cincr cstate ie = incr cstate "cindex" ie
let zincr cstate ie = incr cstate "zindex" ie

let major cstate = access cstate "major"
			
(* [x.cont.(i1)....(in).(j1)...(jk) <- cstate.cvec.(pos)] *)
(* [x.zero_in.(i1)...(in).(j1)...(jk) <- cstate.zin.(pos)] *)

let write_into_internal_state (x, cont) i_list j_list get pos =
  Eassign_state
    (left_state_access
       (left_state_access
	  (Eleft_state_primitive_access(Eleft_state_name(x), cont))
          i_list) j_list, get (varmut pos))
    
let app f arg_list = Eapp { f = global(modname f); arg_list }
let getc cstate pos =
  app "get" [access cstate "cvec"; pos]
let get_zin cstate pos =
  app "get_zin" [access cstate "zinvec"; pos]
let setc cstate pos e =
  app "set" [access cstate "cvec"; pos; e]
let setd cstate pos e =
  app "set" [access cstate "dvec"; pos; e]
let set_zout cstate pos e =
  app "set" [access cstate "zoutvec"; pos; e]

(* sets the continuous state vector - from the csolver to the internal state *)
let cin cstate x i_list j_list pos =
  let getc pos = getc cstate pos in
  write_into_internal_state (x, Epos) i_list j_list getc pos
			    
(* sets the zero-crossing vector - from the zsolver to the internal state *)
let zin cstate x i_list j_list pos =
  let get_zin pos = get_zin cstate pos in
  write_into_internal_state (x, Ezero_in) i_list j_list get_zin pos

(* [cstate.cvec.(pos) <- (x.cont.(i1)....(in)).(j1)...(jk)] *)
(* [cstate.dvec.(pos) <- (x.der.(i1)....(in)).(j1)...(jk)] *)
(* [cstate.zout.(pos) <- (x.zout.(i1)....(in)).(j1)...(jk)] *)
let write_from_internal_state set (x, cont) i_list j_list pos =
  set (varmut pos)
    (Estate
       (left_state_access
          (left_state_access
	     (Eleft_state_primitive_access(Eleft_state_name(x), cont))
	     i_list) j_list))
let cout cstate x i_list j_list pos =
  let setc pos e = setc cstate pos e in
  write_from_internal_state setc (x, Epos) i_list j_list pos
let dout cstate x i_list j_list pos =
  let setd pos e = setd cstate pos e in
  write_from_internal_state setd (x, Eder) i_list j_list pos
let zout cstate x i_list j_list pos =
  let set_zout pos e = set_zout cstate pos e in
  write_from_internal_state set_zout (x, Ezero_out) i_list j_list pos
let set_zin_to_false x i_list j_list pos =
  Eassign_state
    (left_state_access
       (left_state_access
          (Eleft_state_primitive_access(Eleft_state_name(x), Ezero_in))
          i_list) j_list,
     ffalse)

let set_dvec_to_zero cstate c_start csize =
  if is_zero csize then void
  else Efor { dir = true; index = i; left = local c_start;
              right = minus_opt csize one;
              e = setd cstate (local i) (float_const 0.0) }

(** Compute the index associated to a state variable [x] in the current block *)
(* [build_index m_list = (ctable, csize), (ztable, zsize), h_opt, major_opt] *)
let build_index m_list =
  (* [increase size typ e_list = size'] such that
   *- size' = size + (size_of typ) * s1 * ... * sn.
   *- E.g., cont x[e1]...[en]: t is a vector of dimension n of a value t
   *- t can itself be a floatting point vector of dimension k 
      (size m1 * ... * mk).
   *- In that case (size_of t = [m1]...[mk]
   *- for cont x[]: t, the size is that of t
         build two tables. The table [ctable] associates a pair
   *- ([m1]...[mk], [e1]...[en]) to every continuous state variable; 
   *- [ztable] do the same for zero-crossings
   *- the variable [h_opt] which defines the next horizon
   *- the variable [major_opt] which is true in a discrete mode
   *- the variable [time_opt] defines the current time *)
  let size s = Translate.exp_of_sizetype s in
  let build ((ctable, ztable, h_opt, major_opt, time_opt) as acc)
	    { m_typ = typ; m_name = n; m_kind = m; m_size = e_list } = 
    let add_opt v opt =
      match opt with
      | None -> Some(v)
      | Some(w) -> Misc.internal_error "Inout" Ident.fprint_t w in
    match m with
    | None -> acc
    | Some(k) ->
       match k with
       | Horizon -> ctable, ztable, add_opt n h_opt, major_opt, time_opt
       | Major -> ctable, ztable, h_opt, add_opt n major_opt, time_opt
       | Time ->
          ctable, ztable, h_opt, major_opt, add_opt n time_opt
       | Period | Encore -> acc
       | Zero ->
	  let s_list = Types.sizes_per_dimension typ in
          ctable, Env.add n (List.map size s_list, e_list) ztable,
	  h_opt, major_opt, time_opt
       | Cont ->
	  let s_list = Types.sizes_per_dimension typ in
	  let ctable = Env.add n (List.map size s_list, e_list) ctable in
          ctable, ztable, h_opt, major_opt, time_opt in
       
  let ctable, ztable, h_opt, major_opt, time_opt =
    List.fold_left build (Env.empty, Env.empty, None, None, None) m_list in
  ctable, ztable, h_opt, major_opt, time_opt

(* Compute the size of a table *)
let size_of table =
  let size _ (s_list, e_list) acc =
    let s1 =
      List.fold_left (fun acc s -> mult_opt acc s) one s_list in
    let s2 = List.fold_left mult_opt s1 e_list in
    plus_opt acc s2 in
  Env.fold size table zero
	   
(* Add a method to copy back and forth the internal representation
 *- of the continuous state vector to the external flat representation
 *- This function is generic: table contains the association table
 *- [name, ([s1]...[sn], [e1]...[ek])]. *)
let cinout table call pos incr =
  (* For every input x associated to ([s1]...[sn], [e1]...[ek])) from [table] *)
  (* for i1 = 0 to s1 - 1 do
   *-  ...
   *-  for in = 0 to sn - 1 do
   *-    for j1 = 0 to e1 do
   *-    ...
   *-      for jk = 0 to ek - 1 do
   *-        call (local x) i1...in j1...jk pos; incr pos
   *-      done
   *-    done
   *-  done
   *- done *)
  let rec copy i_list e_list body =
    match i_list, e_list with
    | [], [] -> body
    | i :: i_list, e :: e_list ->
       Efor { dir = true; index = i; left = int_const 0;
              right = e; e = copy i_list e_list body }
    | _ -> assert false in

  let add x (s_list, e_list) acc =
    let i_list = List.map (fun _ -> Ident.fresh "i") s_list in
    let j_list = List.map (fun _ -> Ident.fresh "j") e_list in
    (copy i_list s_list
	  (copy j_list e_list
		(sequence [call x i_list j_list pos; incr pos]))) :: acc in
  let c_list = Env.fold add table [] in
  sequence(c_list)

let cin table cstate pos =
  let call x i_list j_list pos = cin cstate x i_list j_list pos in
  cinout table call pos incr_pos

let cout table cstate pos =
  let call x i_list j_list pos = cout cstate x i_list j_list pos in
  cinout table call pos incr_pos

let dout table cstate pos =
  let call x i_list j_list pos = dout cstate x i_list j_list pos in
  cinout table call pos incr_pos

let zin table cstate pos =
  let call x i_list j_list pos = zin cstate x i_list j_list pos in
  cinout table call pos incr_pos

let zout table cstate pos =
  let call x i_list j_list pos = zout cstate x i_list j_list pos in
  cinout table call pos incr_pos

let set_zin_to_false table pos =
   let call x i_list j_list pos = set_zin_to_false x i_list j_list pos in
   cinout table call pos (fun _ -> void)
 
(* increments the maximum size of the continuous state vector and that of *)
(* the zero-crossing vector *)
let maxsize call size i_opt =
  if is_zero size then i_opt
  else let i = call size in
       match i_opt with
       | None -> Some(i) | Some(i_old) -> Some(sequence [i; i_old])

(* If the current block contains an horizon state variable *)
(* for every horizon state variable *)
let set_horizon cstate h_opt =
  match h_opt with
  | None -> Econst(Evoid) | Some(h) -> set_horizon cstate h

(* If the current block contains a major state variable *)
let set_major cstate major_opt =
  match major_opt with
  | None -> Econst(Evoid) | Some(m) -> set_major cstate m

(* If the current block contains a reference to time *)
let set_time cstate time_opt =
  match time_opt with
  | None -> Econst(Evoid) | Some(m) -> set_time cstate m

(* Translate a continuous-time machine *)
let hybrid_machine 
    ({ ma_params = params; ma_initialize = i_opt; ma_memories = m_list;
       ma_instances = mi_list; ma_methods = method_list } as mach) =
  let cstate = Ident.fresh "cstate" in
  (* auxiliary function. Find the method "step" in the list of methods *)
  let rec find_step method_list =
    match method_list with
    | [] -> raise Not_found
    | { me_name = m } as mdesc :: method_list ->
       if m = Oaux.step then mdesc, method_list
       else let step, method_list = find_step method_list in
	    step, mdesc :: method_list in
  (* for every instance of a continuous machine () *)
  (* pass the extra argument [cstate] *)
  let add_extra_param ({ i_kind = k; i_params = params } as ientry) =
    match k with
    | Tnode(Tcont) -> { ientry with i_params = (local cstate) :: params }
    | _ -> ientry in
  try
    let { me_body = body; me_typ = ty } as mdesc, method_list =
      find_step method_list in
    (* associate an integer index to every continuous state *)
    (* variable and zero-crossing *)
    let ctable, ztable, h_opt, major_opt, time_opt = build_index m_list in

    let csize = size_of ctable in
    let zsize = size_of ztable in
    
    let c_is_not_zero = not (is_zero csize) in
    let z_is_not_zero = not (is_zero zsize) in
    let h_is_not_zero = not (h_opt = None) in
    let major_is_not_zero = not (major_opt = None) in
    let time_is_not_zero = not (time_opt = None) in
    
    (* add initialization code to [e_opt] *)
    let i_opt =
      maxsize (cmax cstate) csize (maxsize (zmax cstate) zsize i_opt) in
          
    let c_start = Ident.fresh "cindex" in
    let z_start = Ident.fresh "zindex" in
    let cstate_cpos = access cstate "cindex" in
    let cstate_zpos = access cstate "zindex" in
    
    let cpos = Ident.fresh "cpos" in
    let zpos = Ident.fresh "zpos" in
    let result = Ident.fresh "result" in

    let letin_only cond pat e body =
      if cond then letin pat e body else body in
    let letvar_only cond v ty e body =
      if cond then letvar v ty e body else body in
    let only cond inst = if cond then inst else void in
    let only_else cond inst1 inst2 = if cond then inst1 else inst2 in
        
    let typ_int = Interface.type_expression_of_typ Initial.typ_int in
    let body =
      letin_only c_is_not_zero
        (* compute the current position of the cvector *)
	(varpat c_start typ_int) cstate_cpos
        (letvar_only
           c_is_not_zero cpos Initial.typ_int (local c_start)
	   (* compute the current position of the zvector *)
           (letin_only
              z_is_not_zero (varpat z_start typ_int) cstate_zpos
              (letvar_only
                 z_is_not_zero zpos Initial.typ_int (local z_start)
		 (sequence
		    [only c_is_not_zero (incr cstate "cindex" csize);
                     only z_is_not_zero (incr cstate "zindex" zsize);
		     only major_is_not_zero (set_major cstate major_opt);
		     only time_is_not_zero (set_time cstate time_opt);
		     ifthenelse
                       (major cstate) (set_dvec_to_zero cstate c_start csize)
		       (only c_is_not_zero (cin ctable cstate cpos));
                     (only_else
                        (c_is_not_zero || z_is_not_zero || h_is_not_zero)
                        (letin
		           (varpat result (Interface.type_expression_of_typ ty))
                           body
		           (sequence
			      [set_horizon cstate h_opt;
                               only
                                 c_is_not_zero (set cpos (local c_start));
	                       ifthenelse
                                 (major cstate)
				 (sequence
                                   [only
                                      c_is_not_zero (cout ctable cstate cpos);
                                    only
                                      z_is_not_zero
                                      (set_zin_to_false ztable zpos)])
                                 (sequence
				    [only
                                       z_is_not_zero (zin ztable cstate zpos);
                                     only
                                       z_is_not_zero
                                       (set zpos (local z_start));
	                             only
                                       z_is_not_zero (zout ztable cstate zpos);
	                             only
                                       c_is_not_zero (dout ctable cstate cpos)]);
                               local result]))
                        body)
        ])))) in
    { mach with ma_params = (Evarpat { id = cstate; ty = typ_cstate }) :: params;
		ma_initialize = i_opt;
		ma_methods = { mdesc with me_body = body } :: method_list;
		ma_instances = List.map add_extra_param mi_list }
  with
    (* no step method is present *)
    Not_found -> mach

let machine({ ma_kind } as mach) =
  match ma_kind with
  | Deftypes.Tnode(Tcont) -> hybrid_machine mach
  | _ -> mach

let rec exp e = match e with
  | Econst _ | Econstr0 _ | Eglobal _ | Evar _ | Estate _ -> e
  | Econstr1 { lname; arg_list } ->
     Econstr1 { lname; arg_list = List.map exp arg_list }
  | Etuple(e_list) -> Etuple(List.map exp e_list)
  | Erecord(r_list) ->
     Erecord(List.map (fun { label; arg } -> { label; arg = exp arg }) r_list)
  | Erecord_access { arg; label } -> Erecord_access { arg = exp arg; label }
  | Erecord_with(e, r_list) ->
     Erecord_with(exp e,
                  List.map (fun { label; arg } -> { label; arg = exp arg })
                    r_list)
  | Eifthenelse(e1,e2,e3) ->
     Eifthenelse(exp e1, exp e2, exp e3)
  | Ematch(e, m_h_list) ->
     Ematch(exp e,
            List.map (fun { m_pat; m_body } -> { m_pat; m_body = exp m_body })
            m_h_list)
  | Elet(p, e1, e2) -> Elet(p, exp e1, exp e2)
  | Eletvar({ e_opt; e } as l) ->
     Eletvar({ l with e_opt = Util.optional_map exp e_opt; e = exp e })
  | Eletmem(m_list, e) -> Eletmem(m_list, exp e)
  | Eletinstance(i_list, e) -> Eletinstance(i_list, exp e)
  | Eassign(lv, e) -> Eassign(lv, exp e)
  | Eassign_state(lsv, e) -> Eassign_state(lsv, exp e)
  | Esequence(e_list) -> Esequence(List.map exp e_list)
  | Eapp { f; arg_list } -> Eapp { f = exp f; arg_list = List.map exp arg_list }
  | Emethodcall(m_call) -> e
  | Etypeconstraint(e, ty) -> Etypeconstraint(exp e, ty)
  | Efor({ left; right; e } as f) ->
     Efor({ f with left = exp left; right = exp right; e = exp e })
  | Ewhile { cond; e } -> Ewhile { cond = exp cond; e = exp e }
  | Eassert(e) -> Eassert(exp e)
  | Emachine(m) -> Emachine(machine m)
  | Efun { pat_list; e } -> Efun { pat_list; e = exp e }
  | Eget { e; index } -> Eget { e = exp e; index = exp index }
  | Eupdate { e; size; index; arg } ->
     Eupdate { e = exp e; size = exp size; index = exp index; arg = exp arg }
  | Eslice { e; left; right } ->
     Eslice { e = exp e; left = exp e; right = exp e }
  | Econcat { left; left_size; right; right_size } ->
     Econcat { left = exp left; left_size = exp left_size;
               right = exp right; right_size = exp right_size }
  | Evec { e; size } -> Evec { e = exp e; size = exp size }
  | Eletsizefun(is_rec, sizefun_list, e) ->
     Eletsizefun(is_rec, List.map sizefun sizefun_list, exp e)
  | Esizeapp { f; size_list } ->
     Esizeapp { f = exp f; size_list = List.map exp size_list }

and sizefun ({ sf_e } as f) = { f with sf_e = exp sf_e }

(* The main entry. Add new methods to copy the continuous state vector *)
(* back and forth into the internal state *)
let implementation impl =
  match impl with
  | Eletdef(n_e_list) ->
     Eletdef(List.map (fun (n, e) -> (n, exp e)) n_e_list)
  | Eopen _ | Etypedecl _ -> impl
									 
let implementation_list impl_list = Util.iter implementation impl_list

let program { p_impl_list } =
  { p_impl_list = implementation_list p_impl_list }
