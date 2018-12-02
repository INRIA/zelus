(**************************************************************************)
(*                                                                        *)
(*                                Zelus                                   *)
(*               A synchronous language for hybrid systems                *)
(*                       http://zelus.di.ens.fr                           *)
(*                                                                        *)
(*                    Marc Pouzet and Timothy Bourke                      *)
(*                                                                        *)
(*  Copyright 2012 - 2018. All rights reserved.                           *)
(*                                                                        *)
(*  This file is distributed under the terms of the CeCILL-C licence      *)
(*                                                                        *)
(*  Zelus is developed in the INRIA PARKAS team.                          *)
(*                                                                        *)
(**************************************************************************)

(* add extra code for in-place modification of the continuous state vector *)

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
(*    method csize = ...                                   *)
(*    method zsize = ...                                   *)
(*                                                         *)
(* the body of the step method is extended to read/write   *)
(* entries from the following data-structure               *)
(* on the global parameter cstate                          *)
(* type cstate =
 *-  { dvec : float array;
 *-    cvec : float array;
 *-    zin : bool array;
 *-    zout : float array;
 *-    mutable cpos : int;
 *-    mutable zpos : int;
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
 *-    let c_start = g.cpos in (* current position of the cvector *)
 *-    var cpos = c_start in
 *-    let z_start = g.zpos in (* current position of the zvector *)
 *-    g.cpos <- g.cpos + csize; g.zpos <- g.zpos + zsize;
 *-    var zpos = z_start in
 *-    if d then dzero g.dvec c_start csize (* set all speeds to 0.0 *)
 *-    else ((* sets de value of continuous zero-crossing with what has been *)
 *-          (* computed by the zero-crossing detection *)
 *-          cin g x1 ci;...; cin xn (ci+size1+...+size(n-1)));
 *-          ... cpos is incremented
 *-    let result = ...body... in
 *-    cpos <- c_start;
 *-    if d then 
 *-        (cout g x1 ci;...; cout g ck (zi+size'1+...+size'(n-1));
 *-        ... cpos is incremented)
 *-        g.horizon <- min g.horizon h 
 *-              (* h is the horizon of the block *)
 *-        (* sets the output state vector with the xi *)
 *-        m1 <- false; ...; mk <- false;
 *-        ... zpos is incremented
 *-    else (zin g m1 zi;...; zin g mk (zi+size'1+...+size'(k-1));
 *-          ... zpos is incremented
 *-          zpos <- z_start;
 *-          zout m1 zi;...; mout mk (zi+size'1+...+size'(k-1));
 *-          ... zpos is incremented
 *-          dout g x1 ci;...; xout ck (zi+size'1+...+size'(n-1));
 *-          ... zpos is incremented);
 *-      (* store the argument of zero-crossing into the vector of zero-cross *)
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

let set_horizon g h =
  Oassign(Oleft_record_access(Oleft_name(g), Name "horizon"),
          omin (Orecord_access(var g, Name "horizon"))
            (Ostate(Oleft_state_name h)))
                   
(* [x := !x + 1] *)
let incr_pos x = Oassign(Oleft_name x, oplus (var x) one)
let set_pos x e = Oassign(Oleft_name x, e)

(* [g.field <- g.field + i] *)
let incr g field ie =
  Oassign(Oleft_record_access(Oleft_name g, Name(field)),
          oplus (Orecord_access(Olocal(g), Name(field))) ie)
               
let cmax g ie = incr g "cmax" ie
let zmax g ie = incr g "zmax" ie
let cincr g ie = incr g "cpos" ie
let zincr g ie = incr g "zpos" ie

let discrete g = Orecord_access(var g, Name("discrete"))
			
(* [x.cont.(i1)....(in).(j1)...(jk) <- g.cvec.(pos)] *)
(* x.zero_in.(i1)...(in).(j1)...(jk) <- g.zin.(pos) *)
let write_into_internal_state (x, cont) i_list j_list (g, field) pos =
  Oassign_state
    (left_state_access
       (left_state_access
	  (Oleft_state_primitive_access(Oleft_state_name(x), cont))
	  i_list) j_list, Oaccess(Orecord_access(var g, Name(field)), var pos))
let cin g x i_list j_list pos =
  write_into_internal_state (x, Ocont) i_list j_list (g, "cvec") pos
let zin g x i_list j_list pos =
  write_into_internal_state (x, Ozero_in) i_list j_list (g, "zin") pos

(* [g.cvec.(pos) <- (x.cont.(i1)....(in)).(j1)...(jk)] *)
(* [g.dvec.(pos) <- (x.der.(i1)....(in)).(j1)...(jk)] *)
(* [g.zout.(pos) <- (x.zout.(i1)....(in)).(j1)...(jk)] *)
let write_from_internal_state (g, field) (x, cont) i_list j_list pos =
  Oassign
    (Oleft_index(Oleft_record_access(Oleft_name(g), Name(field)), var pos),
     (Ostate
         (left_state_access
           (left_state_access
              (Oleft_state_primitive_access(Oleft_state_name(x), cont))
	      i_list) j_list)))
let cout g x i_list j_list pos =
  write_from_internal_state (g, "cvec") (x, Ocont) i_list j_list pos
let dout g x i_list j_list pos =
  write_from_internal_state (g, "dvec") (x, Oder) i_list j_list pos
let zout g x i_list j_list pos =
  write_from_internal_state (g, "zout") (x, Ozero_out) i_list j_list pos
let set_zin_to_false x i_list j_list pos =
  Oassign_state
    (left_state_access
       (left_state_access
          (Oleft_state_primitive_access(Oleft_state_name(x), Ozero_in))
          i_list) j_list,
     ffalse)
let set_dvec_to_zero g c_start csize =
  if is_zero csize then Oexp(void)
  else Ofor(true, i, local c_start, minus csize one,
            Oassign(Oleft_index(Oleft_record_access(Oleft_name(g), Name "dvec"),
				local i),
            float_const 0.0))

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

let cin table g pos =
  let call x i_list j_list pos = cin g x i_list j_list pos in
  cinout table call pos incr_pos

let cout table g pos =
  let call x i_list j_list pos = cout g x i_list j_list pos in
  cinout table call pos incr_pos

let dout table g pos =
  let call x i_list j_list pos = dout g x i_list j_list pos in
  cinout table call pos incr_pos

let zin table g pos =
  let call x i_list j_list pos = zin g x i_list j_list pos in
  cinout table call pos incr_pos

let zout table g pos =
  let call x i_list j_list pos = zout g x i_list j_list pos in
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
let set_horizon g h_list =
  sequence (List.map (set_horizon g) h_list)
           
(** Translate a continuous-time machine *)
let machine f ({ ma_initialize = i_opt;
		 ma_memories = m_list; ma_methods = method_list } as mach) g =
  (* auxiliary function. Find the method "step" in the list of methods *)
  let rec find_step method_list =
    match method_list with
    | [] -> raise Not_found
    | { me_name = m } as mdesc :: method_list ->
       if m = Ostep then mdesc, method_list
       else let step, method_list = find_step method_list in
	    step, mdesc :: method_list in
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
    (* let i_opt = maxsize cmax csize (maxsize zmax zsize i_opt) in *)
          
    let c_start = Ident.fresh "c_start" in
    let z_start = Ident.fresh "z_start" in
    let g_cpos = Orecord_access(var g, Name("cpos")) in
    let g_zpos = Orecord_access(var g, Name("zpos")) in
    
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
	(varpat c_start Initial.typ_int) g_cpos
        (oletvar_only
           c_is_not_zero cpos Initial.typ_int (local c_start)
	   (* compute the current position of the zvector *)
           (oletin_only
              z_is_not_zero (varpat z_start Initial.typ_int) g_zpos
              (oletvar_only
                 z_is_not_zero zpos Initial.typ_int (local z_start)
		 (sequence
		    [only c_is_not_zero (incr g "csize" csize);
                     only z_is_not_zero (incr g "zsize" zsize);
		     ifthenelse
                       (discrete g) (set_dvec_to_zero g c_start csize)
		       (only c_is_not_zero (cin ctable g cpos));
                     (only_else
                        (c_is_not_zero || z_is_not_zero || h_is_not_zero)          
                        (oletin
		           (varpat result ty) (Oinst(body))
		           (sequence
			      [set_horizon g h_list;
                               only
                                 c_is_not_zero (set_pos cpos (local c_start));
			       ifthenelse (discrete g)
				          (sequence
                                             [only
                                                c_is_not_zero (cout ctable g cpos);
                                              only
                                                z_is_not_zero
                                                (set_zin_to_false ztable zpos)])
				          (sequence
					     [only
                                                z_is_not_zero (zin ztable g zpos);
                                              only
                                                z_is_not_zero
                                                (set_pos zpos (local z_start));
			                      only
                                                z_is_not_zero (zout ztable g zpos);
					      only
                                                c_is_not_zero (dout ctable g cpos)]);
                               Oexp (local result)]))
                        body)])))) in
            { mach with ma_initialize = i_opt;
		        ma_methods = { mdesc with me_body = body } :: method_list }
            with
              (* no get method is present *)
              Not_found -> mach

                       
(** The main entry. Add new methods to copy the continuous state vector *)
(** back and forth into the internal state *)
let implementation impl =
  match impl with
  | Oletmachine(f, ({ ma_kind = Deftypes.Tcont } as mach)) -> 
     (* only continuous machines are concerned *)
     Oletmachine(f, machine f mach)
  | Oletmachine _ | Oletvalue _ | Oletfun _ | Oopen _ | Otypedecl _ -> impl
									 
let implementation_list impl_list = Misc.iter implementation impl_list
