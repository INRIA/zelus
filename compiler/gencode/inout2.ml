(**************************************************************************)
(*                                                                        *)
(*                                Zelus                                   *)
(*               A synchronous language for hybrid systems                *)
(*                       http://zelus.di.ens.fr                           *)
(*                                                                        *)
(*                    Marc Pouzet and Timothy Bourke                      *)
(*                                                                        *)
(*  Copyright 2012 - 2019. All rights reserved.                           *)
(*                                                                        *)
(*  This file is distributed under the terms of the CeCILL-C licence      *)
(*                                                                        *)
(*  Zelus is developed in the INRIA PARKAS team.                          *)
(*                                                                        *)
(**************************************************************************)

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
 *-    mutable discrete : bool }                           *)

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
 *-    var zpos = z_start in
 *-    if cstate.discrete then 
 *-        dzero cstate.dvec c_start csize (* set all speeds to 0.0 *)
 *-    else ((* copy the value of the continuous state vector of the solver *)
 *-          (* into the local continuous state variables *)
 *-          cin cstate x1 ci;...; cin xn (ci+size1+...+size(n-1)));
 *-          ... cpos is incremented
 *-    let result = ...body... in
 *-    cpos <- c_start;
 *-    if cstate.discrete then 
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
open Format

let typ_cstate = Otypeconstr(Modname {qual = "Ztypes"; id = "cstate" }, [])

let oletin p e1 i2 = Olet(p, e1, i2)
let oletvar x ty e1 i2 = Oletvar(x, false, ty, Some(e1), i2)
let bool v = Oconst(Obool(v))
let int_const v = Oconst(Oint(v))
let float_const v = Oconst(Ofloat(v))
let operator op = Oglobal(Modname (Initial.pervasives_name op))
let oplus e1 e2 = Oapp(operator "+", [e1; e2])
let omult e1 e2 = Oapp(operator "*", [e1; e2])
let ominus e1 e2 = Oapp(operator "-", [e1; e2])
let omin e1 e2 = Oapp(operator "min", [e1; e2])
let zero = int_const 0
let one = int_const 1
let ffalse = bool false
let is_zero e = match e with Oconst(Oint(0)) -> true | _ -> false
let plus e1 e2 =
  match e1, e2 with
  | Oconst(Oint(0)), _ -> e2
  | _, Oconst(Oint(0)) -> e1
  | Oconst(Oint(v1)), Oconst(Oint(v2)) -> Oconst(Oint(v1 + v2))
  | _ -> oplus e1 e2
let minus e1 e2 =
  match e1, e2 with
  | _, Oconst(Oint(0)) -> e1
  | Oconst(Oint(v1)), Oconst(Oint(v2)) -> Oconst(Oint(v1 - v2))
  | _ -> ominus e1 e2
let mult e1 e2 =
  match e1, e2 with
  | Oconst(Oint(1)), _ -> e2
  | _, Oconst(Oint(1)) -> e1
  | Oconst(Oint(v1)), Oconst(Oint(v2)) -> Oconst(Oint(v1 * v2))
  | _ -> omult e1 e2
let min e1 e2 = Oapp(operator "min", [e1; e2])
let local x = Olocal(x)
let modname x = Lident.Modname { Lident.qual = "Zls"; Lident.id = x }
let global x = Oglobal(x)                      
let varpat x ty = Ovarpat(x, Translate.type_expression_of_typ ty)
let var x = Ovar(false, x)
let varmut x = Ovar(true, x)
let void = Oconst(Ovoid)
let ifthenelse c i1 i2 =
  match i1, i2 with
  | Oexp(Oconst(Ovoid)), Oexp(Oconst(Ovoid)) -> Oexp(Oconst(Ovoid))
  | _, Oexp(Oconst(Ovoid)) -> Oif(c, i1, None)
  | _ -> Oif(c, i1, Some(i2))
let sequence i_list =
  let seq i i_list =
    match i, i_list with
    | Oexp(Oconst(Ovoid)), _ -> i_list
    | _, [] -> [i]
    | _ -> i :: i_list in
  let i_list = List.fold_right seq i_list [] in
  match i_list with
  | [] -> Oexp(void)
  | _ -> Osequence i_list
                   
let rec left_state_access lv i_list =
  match i_list with
  | [] -> lv
  | i :: i_list -> left_state_access (Oleft_state_index(lv, local i)) i_list
				     
let i = Ident.fresh "i"

(* Convert a size into an expression *)
let rec size s =
  match s with
  | Sconst(i) -> Oconst(Oint(i))
  | Sglobal(ln) -> Oglobal(ln)
  | Sname n -> Olocal(n)
  | Sop(op, s1, s2) ->
     let s1 = size s1 in
     let s2 = size s2 in
     match op with
     | Splus -> plus s1 s2
     | Sminus -> minus s1 s2

let set_horizon cstate h =
  Oassign(Oleft_record_access(Oleft_name(cstate), Name "horizon"),
          omin (Orecord_access(varmut cstate, Name "horizon"))
            (Ostate(Oleft_state_name h)))
                   
(* [x := !x + 1] *)
let incr_pos x = Oassign(Oleft_name x, oplus (var x) one)
let set_pos x e = Oassign(Oleft_name x, e)

(* [cstate.field <- cstate.field + i] *)
let incr cstate field ie =
  Oassign(Oleft_record_access(Oleft_name cstate, Name(field)),
          oplus (Orecord_access(Olocal(cstate), Name(field))) ie)
             
let cmax cstate ie = incr cstate "cmax" ie
let zmax cstate ie = incr cstate "zmax" ie
let cincr cstate ie = incr cstate "cindex" ie
let zincr cstate ie = incr cstate "zindex" ie

let discrete cstate = Orecord_access(varmut cstate, Name("discrete"))
			
(* [x.cont.(i1)....(in).(j1)...(jk) <- cstate.cvec.(pos)] *)
(* [x.zero_in.(i1)...(in).(j1)...(jk) <- cstate.zin.(pos)] *)

let write_into_internal_state (x, cont) i_list j_list get pos =
  Oassign_state
    (left_state_access
       (left_state_access
	  (Oleft_state_primitive_access(Oleft_state_name(x), cont))
          i_list) j_list, get (var pos))
    
let app f args = Oapp(global(modname f), args)
let getc cstate pos =
  app "get" [Orecord_access(varmut cstate, Name("cvec")); pos]
let get_zin cstate pos =
  app "get_zin" [Orecord_access(varmut cstate, Name("zinvec")); pos]
let setc cstate pos e =
  app "set" [Orecord_access(varmut cstate, Name("cvec")); pos; e]
let setd cstate pos e =
  app "set" [Orecord_access(varmut cstate, Name("dvec")); pos; e]
let set_zout cstate pos e =
    app "set" [Orecord_access(varmut cstate, Name("zoutvec")); pos; e]

let cin cstate x i_list j_list pos =
  let getc pos = getc cstate pos in
  write_into_internal_state (x, Ocont) i_list j_list getc pos
			    
let zin cstate x i_list j_list pos =
  let get_zin pos = get_zin cstate pos in
  write_into_internal_state (x, Ozero_in) i_list j_list get_zin pos

(* [cstate.cvec.(pos) <- (x.cont.(i1)....(in)).(j1)...(jk)] *)
(* [cstate.dvec.(pos) <- (x.der.(i1)....(in)).(j1)...(jk)] *)
(* [cstate.zout.(pos) <- (x.zout.(i1)....(in)).(j1)...(jk)] *)
let write_from_internal_state set (x, cont) i_list j_list pos =
  Oexp
    (set (var pos)
	 (Ostate
	    (left_state_access
               (left_state_access
		  (Oleft_state_primitive_access(Oleft_state_name(x), cont))
		  i_list) j_list)))
let cout cstate x i_list j_list pos =
  let setc pos e = setc cstate pos e in
  write_from_internal_state setc (x, Ocont) i_list j_list pos
let dout cstate x i_list j_list pos =
  let setd pos e = setd cstate pos e in
  write_from_internal_state setd (x, Oder) i_list j_list pos
let zout cstate x i_list j_list pos =
  let set_zout pos e = set_zout cstate pos e in
  write_from_internal_state set_zout (x, Ozero_out) i_list j_list pos
let set_zin_to_false x i_list j_list pos =
  Oassign_state
    (left_state_access
       (left_state_access
          (Oleft_state_primitive_access(Oleft_state_name(x), Ozero_in))
          i_list) j_list,
     ffalse)

let set_dvec_to_zero cstate c_start csize =
  if is_zero csize then Oexp(void)
  else Ofor(true, i, local c_start, minus csize one,
            Oexp(setd cstate (local i) (float_const 0.0)))

(** Compute the index associated to a state variable [x] in the current block *)
(* [build_index m_list = (ctable, csize), (ztable, zsize), h_list] *)
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
   * and the list of variables [h_list] which define the next horizon *)
  let size s = size (Translate.size_of_type s) in
  let build (ctable, ztable, h_list)
	    { m_typ = typ; m_name = n; m_kind = m; m_size = e_list } = 
    match m with
    | None -> ctable, ztable, h_list
    | Some(k) ->
       match k with
       | Horizon -> ctable, ztable, n :: h_list
       | Period | Encore -> ctable, ztable, h_list
       | Zero ->
	  let s_list = Types.size_of typ in
        ctable, Env.add n (List.map size s_list, e_list) ztable, h_list
       | Cont ->
	  let s_list = Types.size_of typ in
	  Env.add n (List.map size s_list, e_list) ctable, ztable, h_list in
  let ctable, ztable, h_list =
    List.fold_left build (Env.empty, Env.empty, []) m_list in
  ctable, ztable, h_list

(* Compute the size of a table *)
let size_of table =
  let size _ (s_list, e_list) acc =
    let s1 =
      List.fold_left (fun acc s -> mult acc s) one s_list in
    let s2 = List.fold_left mult s1 e_list in
    plus acc s2 in
  Env.fold size table zero
	   
(** Add a method to copy back and forth the internal representation
 *- of the continuous state vector to the external flat representation
 *- This function is generic: table contains the association table
 *- [name, ([s1]...[sn], [e1]...[ek]). *)
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
       Ofor(true, i, int_const 0, e, copy i_list e_list body)
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
   cinout table call pos (fun _ -> Oexp(void))
 
(* increments the maximum size of the continuous state vector and that of *)
(* the zero-crossing vector *)
let maxsize call size i_opt =
  if is_zero size then i_opt
  else let i = call size in
       match i_opt with
       | None -> Some(i) | Some(i_old) -> Some(sequence [i; i_old])

(* If the current block contains an horizon state variable *)
(* for every horizon state variable *)
let set_horizon cstate h_list =
  sequence (List.map (set_horizon cstate) h_list)
           
(** Translate a continuous-time machine *)
let machine f
    ({ ma_params = params; ma_initialize = i_opt; ma_memories = m_list;
       ma_instances = mi_list; ma_methods = method_list } as mach) cstate =
  (* auxiliary function. Find the method "step" in the list of methods *)
  let rec find_step method_list =
    match method_list with
    | [] -> raise Not_found
    | { me_name = m } as mdesc :: method_list ->
       if m = Ostep then mdesc, method_list
       else let step, method_list = find_step method_list in
	    step, mdesc :: method_list in
  (* for every instance of a continuous machine () *)
  (* pass the extra argument [cstate] *)
  let add_extra_param ({ i_kind = k; i_params = params } as ientry) =
    match k with
    | Tcont -> { ientry with i_params = (varmut cstate) :: params }
    | _ -> ientry in
  try
    let { me_body = body; me_typ = ty } as mdesc, method_list =
      find_step method_list in
    (* associate an integer index to every continuous state *)
    (* variable and zero-crossing *)
    let ctable, ztable, h_list = build_index m_list in

    let csize = size_of ctable in
    let zsize = size_of ztable in
    
    let c_is_not_zero = not (is_zero csize) in
    let z_is_not_zero = not (is_zero zsize) in
    let h_is_not_zero = not (List.length h_list = 0) in
    
    (* add initialization code to [e_opt] *)
    let i_opt =
      maxsize (cmax cstate) csize (maxsize (zmax cstate) zsize i_opt) in
          
    let c_start = Ident.fresh "cindex" in
    let z_start = Ident.fresh "zindex" in
    let cstate_cpos = Orecord_access(varmut cstate, Name("cindex")) in
    let cstate_zpos = Orecord_access(varmut cstate, Name("zindex")) in
    
    let cpos = Ident.fresh "cpos" in
    let zpos = Ident.fresh "zpos" in
    let result = Ident.fresh "result" in

    let oletin_only cond pat e body =
      if cond then oletin pat e body else body in
    let oletvar_only cond v ty e body =
      if cond then oletvar v ty e body else body in
    let only cond inst = if cond then inst else Oexp(void) in
    let only_else cond inst1 inst2 = if cond then inst1 else inst2 in
        
    let body =
      oletin_only c_is_not_zero
        (* compute the current position of the cvector *)
	(varpat c_start Initial.typ_int) cstate_cpos
        (oletvar_only
           c_is_not_zero cpos Initial.typ_int (local c_start)
	   (* compute the current position of the zvector *)
           (oletin_only
              z_is_not_zero (varpat z_start Initial.typ_int) cstate_zpos
              (oletvar_only
                 z_is_not_zero zpos Initial.typ_int (local z_start)
		 (sequence
		    [only c_is_not_zero (incr cstate "cindex" csize);
                     only z_is_not_zero (incr cstate "zindex" zsize);
		     ifthenelse
                       (discrete cstate) (set_dvec_to_zero cstate c_start csize)
		       (only c_is_not_zero (cin ctable cstate cpos));
                     (only_else
                        (c_is_not_zero || z_is_not_zero || h_is_not_zero)
                        (oletin
		           (varpat result ty) (Oinst(body))
		           (sequence
			      [set_horizon cstate h_list;
                               only
                                 c_is_not_zero (set_pos cpos (local c_start));
	                       ifthenelse
                                 (discrete cstate)
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
                                       (set_pos zpos (local z_start));
	                             only
                                       z_is_not_zero (zout ztable cstate zpos);
	                             only
                                       c_is_not_zero (dout ctable cstate cpos)]);
                        Oexp (local result)]))
                        body)])))) in
    { mach with ma_params = (Ovarpat(cstate, typ_cstate)) :: params;
		ma_initialize = i_opt;
		ma_methods = { mdesc with me_body = body } :: method_list;
		ma_instances = List.map add_extra_param mi_list }
  with
    (* no step method is present *)
    Not_found -> mach

                       
(** The main entry. Add new methods to copy the continuous state vector *)
(** back and forth into the internal state *)
let implementation impl =
  match impl with
  | Oletmachine(f, ({ ma_kind = Deftypes.Tcont } as mach)) -> 
     (* only continuous machines are concerned *)
     let cstate = Ident.fresh "cstate" in
     Oletmachine(f, machine f mach cstate)
  | Oletmachine _ | Oletvalue _ | Oletfun _ | Oopen _ | Otypedecl _ -> impl
									 
let implementation_list impl_list = Misc.iter implementation impl_list
