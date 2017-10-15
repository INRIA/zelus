(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2017                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* copie continuous state vectors back and forth into the internal state *)
(* A machine of the form *)
(* machine m =                         *)
(*    memories (k_i m_k: t_i)_{i in I} *)
(*    instance (j_i: f_i)_{i in J}     *)
(*    method (meth_l p_l = e_l)_{l in L} *)
(* is modified by adding functions calls to read and write *)
(* the continous state and zero-crossing vectors *)

(* we suppose known the following globals *)
(*  val cindex : int ref
 *- val zindex : int ref
 *  val cmax : int ref
 *- val zmax : int ref
 *- val cin : cont -> int -> unit
 *- val cout : cont -> int -> unit
 *- val zin : zero -> int -> unit
 *- val zout : zero -> int -> unit
 *- val dzero : int -> int -> unit
 *- val discrete : bool ref
 *- val horizon : float ref *)


(*- let cvec = ref (Zls.cmake 0)
 *- let dvec = ref (Zls.zmake 0)
 *- let zinvec = ref (Zls.cmake 0)
 *- let zoutvec = ref (Zls.zmake 0)
 *- let cindex = ref 0
 *- let cmax = ref 0
 *- let zindex = ref 0
 *- let zmax = ref 0
 *- let discrete = ref true
 *- let horizon = ref infinity
		   
 *- let cindex () = !cindex
 *- let zindex () = !zindex
 *- let cmax i = cmax := !cmax + i
 *- let zmax i = zmax := !zmax + i
 *- let cincr i = cindex := !cindex + i
 *- let zincr i = zindex := !zindex + i
 *- let cin x i = x.pos <- Zls.get !cvec i
 *- let zin x i = x.zin <- Zls.get_zin !zinvec i
 *- let cout x i = Zls.set !cvec i x.pos
 *- let dout x i = Zls.set !dvec i x.der
 *- let zout x i = Zls.set !zout i x.zout
 *- let dzero c s = for i = c to s - 1 do Zls.set !dvec i 0.0 done
 *- let horizon h = horizon := !horizon +. h
 *- let hzero () = horizon := 0.0 *)

(* Only the method "step" is changed and initialization code is added to
 *- set [cmax] and [zmax].
 *- suppose that [csize] is the length of the state vector of the current block;
 *- x1:size1,..., xn:sizen are the continuous state variables;
 *- m1:size'1,..., mk:size'k are the zero-crossing variables;
 *- method step(arg1,...,argl) = ...body... is the step method.
 *- rewrite it into:
 *- method step(arg1,...,argl) =
 *-    let ci = cindex() in (* current position of the cvector *)
 *-    let zi = zindex() in (* current position of the zvector *)
 *-    cindex <- cindex + csize; zindex <- zindex + zsize;
 *-    var cpos = ci in
 *-    var zpos = zi in
 *-    if d then dzero s ci (* set all speeds to 0.0 *)
 *-    else ((* sets de value of continuous zero-crossing with what has been *)
 *-          (* computed by the zero-crossing detection *)
 *-          cin x1 ci;...; cin xn (ci+size1+...+size(n-1)));
 *-          ... cpos is incremented
 *-          (* sets the xi with the value of the input state vector *)
 *-    let result = ...body... in
 *-    cpos := ci;
 *-    if d then 
 *-        (cout x1 ci;...; xout ck (zi+size'1+...+size'(n-1));
 *-        ... cpos is incremented)
 *-        horizon := min (!horizon, h) (* h est l'horizon du bloc *))
 *-        (* sets the output state vector with the xi *)
 *-        m1 <- false; ...; mk <- false;
 *-        ... zpos is incremented
 *-    else (zin m1 zi;...; zout mk (zi+size'1+...+size'(k-1));
 *-          ... zpos is incremented
 *-          zpos := zi;
 *-          zout m1 zi;...; mout mk (zi+size'1+...+size'(k-1));
 *-          ... zpos is incremented)
 *-          dout x1 ci;...; xout ck (zi+size'1+...+size'(n-1));
 *-          ... cpos is incremented);
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

(* input/output functions *)
let bang mname = Oapp(operator "!", [global (modname mname)])
let cindex = bang "cindex"
let zindex = bang "zindex"
let discrete = bang "discrete"

let inout f args = Oapp(global(modname f), args)
let get e i = inout "get" [e; i]
let get_zin e i = inout "get_zin" [e; i]
let set e i arg = inout "set" [e; i; arg]
let set_horizon h =
  Oassign_state(Oleft_state_global(modname "horizon"),
                omin (bang "horizon") (Ostate(Oleft_state_name(h))))
                          
(* [x := !x + 1] *)
let incr_pos x = Oassign(Oleft_name x, oplus (var x) one)
let set_pos x e = Oassign(Oleft_name x, e)

(* [x := !x + i] *)
let incr x ie = Oassign_state(Oleft_state_global(modname x), oplus (bang x) ie)
               
let cmax ie = incr "cmax" ie
let zmax ie = incr "zmax" ie
let cincr ie = incr "cindex" ie
let zincr ie = incr "zindex" ie
                  
(* [x.(i1)....(in).(j1)...(jk) <- !cvec.(pos)] *)
let cin x i_list j_list pos =
  Oassign_state
    (left_state_access
       (left_state_access
	  (Oleft_state_primitive_access(Oleft_state_name(x), Ocont))
	  i_list) j_list,
     get (bang "cvec") (var pos))
let zin x i_list j_list pos =
  Oassign_state
    (left_state_access
       (left_state_access
	  (Oleft_state_primitive_access(Oleft_state_name(x), Ozero_in))
	  i_list) j_list,
     get_zin (bang "zinvec") (var pos))
(* [!cvec.(pos) <- x.(i1)....(in).(j1)...(jk)] *)
let cout x i_list j_list pos =
  set (bang "cvec") (var pos)
      (Ostate(left_state_access
		(left_state_access
		   (Oleft_state_primitive_access(Oleft_state_name(x), Ocont))
		   i_list) j_list))
let dout x i_list j_list pos =
  set (bang "dvec") (var pos)
      (Ostate(left_state_access
		(left_state_access
		   (Oleft_state_primitive_access(Oleft_state_name(x), Oder))
		   i_list) j_list))
let zout x i_list j_list pos =
  set (bang "zoutvec") (var pos)
      (Ostate(left_state_access
		(left_state_access
		   (Oleft_state_primitive_access(Oleft_state_name(x), Ozero_out))
		i_list) j_list))
let zfalse x i_list j_list pos =
  Oassign_state
    (left_state_access
       (left_state_access
          (Oleft_state_primitive_access(Oleft_state_name(x), Ozero_in))
          i_list) j_list,
     ffalse)
let dzero c s =
  if is_zero s then Oexp(void)
  else Ofor(true, i, local c, minus s one,
            Oexp(set (bang "dvec") (local i) (float_const 0.0)))

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

let cin table pos =
  let call x i_list j_list pos = cin x i_list j_list pos in
  cinout table call pos incr_pos

let cout table pos =
  let assign x i_list j_list pos = Oexp(cout x i_list j_list pos) in
  cinout table assign pos incr_pos

let dout table pos =
  let assign x i_list j_list pos = Oexp(dout x i_list j_list pos) in
  cinout table assign pos incr_pos

let zin table pos =
  let assign x i_list j_list pos = zin x i_list j_list pos in
  cinout table assign pos incr_pos

let zout table pos =
  let assign x i_list j_list pos = Oexp(zout x i_list j_list pos) in
  cinout table assign pos incr_pos

let zfalse table pos =
   let assign x i_list j_list pos = zfalse x i_list j_list pos in
   cinout table assign pos (fun _ -> Oexp(void))
 
(* increments the maximum size of the continuous state vector and that of *)
(* the zero-crossing vector *)
let maxsize call size i_opt =
  if is_zero size then i_opt
  else let i = call size in
       match i_opt with
       | None -> Some(i) | Some(i_old) -> Some(sequence [i; i_old])

(* If the current block contains an horizon state variable *)
(* for every horizon state variable *)
let set_horizon h_list =
  sequence (List.map set_horizon h_list)
           
(** Translate a continuous-time machine *)
let machine f ({ ma_initialize = i_opt;
		 ma_memories = m_list; ma_methods = method_list } as mach) =
  (* auxiliary function. Find the method "step" in the list of methods *)
  let rec get method_list =
    match method_list with
    | [] -> raise Not_found
    | { me_name = m } as mdesc :: method_list ->
       if m = Ostep then mdesc, method_list
       else let step, method_list = get method_list in
	    step, mdesc :: method_list in
  try
    let { me_body = body; me_typ = ty } as mdesc, method_list =
      get method_list in
    (* associate an integer index to every continuous state *)
    (* variable and zero-crossing *)
    let ctable, ztable, h_list = build_index m_list in

    let csize = size_of ctable in
    let zsize = size_of ztable in
    
    let c_is_not_zero = not (is_zero csize) in
    let z_is_not_zero = not (is_zero zsize) in
    let h_is_not_zero = not (List.length h_list = 0) in
    
    (* add initialization code to [e_opt] *)
    let i_opt = maxsize cmax csize (maxsize zmax zsize i_opt) in
          
    let ci = Ident.fresh "ci" in
    let zi = Ident.fresh "zi" in
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
	(varpat ci Initial.typ_int) cindex
        (oletvar_only
           c_is_not_zero cpos Initial.typ_int (local ci)
	   (* compute the current position of the zvector *)
           (oletin_only
              z_is_not_zero (varpat zi Initial.typ_int) zindex
              (oletvar_only
                 z_is_not_zero zpos Initial.typ_int (local zi)
		 (sequence
		    [only
                        c_is_not_zero (cincr csize);
                     only
                       z_is_not_zero (zincr zsize);
		     ifthenelse
                       discrete (dzero ci csize)
		       (only c_is_not_zero (cin ctable cpos));
                     (only_else
                        (c_is_not_zero || z_is_not_zero || h_is_not_zero)          
                        (oletin
		           (varpat result ty) (Oinst(body))
		           (sequence
			      [set_horizon h_list;
                               only
                                 c_is_not_zero (set_pos cpos (local ci));
			       ifthenelse discrete
				          (sequence
                                             [only
                                                c_is_not_zero (cout ctable cpos);
                                              only
                                                z_is_not_zero
                                                (zfalse ztable zpos)])
				          (sequence
					     [only
                                                z_is_not_zero (zin ztable zpos);
                                              only
                                                z_is_not_zero
                                                (set_pos zpos (local zi));
			                      only
                                                z_is_not_zero (zout ztable zpos);
					      only
                                                c_is_not_zero (dout ctable cpos)]);
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
