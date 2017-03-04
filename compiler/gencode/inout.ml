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
(* is extended with input/output methods *)
(* machine m =                         *)
(*    memories (k_i m_k: t_i)_{i in I} *)
(*    instance (j_i: f_i)_{i in J}     *)
(*    method (meth_l p_l = e_l)_{l in L} *)
(*    method maxsize: int * int -- returns the max length of the *)
(*                                 cvector and zvector *)
(*    method cin cvec start: int -- copies cvec into the internal state *)
(*    method cout cvec start: int -- copies the internal state into cvec *)
(*    method dout dvec start: int -- copies the internal state into dvec *)
(*    method zin zinvec start: int -- copies zinvec into the internal state *)
(*    method clear_zin -- sets the internal zero-crossings to false *)
(*    method dzero -- sets the internal derivatives to 0.0 *)
(*    method zout zoutvec start: int -- copies the internal state into zoutvec *)

open Misc
open Ident
open Lident
open Deftypes
open Obc
open Format

let infinity = Oglobal(Modname(Initial.pervasives_name "infinity"))
let varpat x ty = Ovarpat(x, Translate.type_expression_of_typ ty)
let tuplepat p_list = Otuplepat(p_list)
let wildpat = Owildpat
let void = Oconst(Ovoid)
let int32_0 = Oconst(Oint32 0)
let tuple e_list = Otuple(e_list)
let var x = Ovar(x)
let local x = Olocal(x)
let state x = Ostate(Oleft_state_name(x))
let int_const v = Oconst(Oint(v))
let float_const v = Oconst(Ofloat(v))
let bool b = Oconst(Obool(b))
let operator op = Oglobal(Modname (Initial.pervasives_name op))
let oplus e1 e2 = Oapp(operator "(+)", [e1; e2])
let omin e1 e2 = Oapp(operator "min", [e1; e2])
let olte e1 e2 = Oapp(operator "(<=)", [e1; e2])
let olt e1 e2 = Oapp(operator "(<)", [e1; e2])
let oneq e1 e2 = Oapp(operator "(<>)", [e1; e2])
let onot e = Oapp(operator "not", [e])
let oand e1 e2 = Oapp(operator "(&&)", [e1; e2])
let oassign id e = Oassign(Oleft_name(id), e)
let oassign_state id e = Oassign_state(Oleft_state_name(id), e)
let oletvar id ty e_opt e = Oletvar(id, ty, e_opt, e)
let owhile e1 e2 = Owhile(e1, e2)
let call o m_name e_list = 
  Omethodcall({ met_machine = None; met_name = m_name;
		met_instance = Some(o, []); met_args = e_list })
let olet p e1 i2 = Olet(p, e1, i2)
let rec olets p_e_list i =
  match p_e_list with | [] -> i | (p, e) :: p_e_list -> olet p e (olets p_e_list i)
let rec sum v e_list =
  match e_list with
  | [] -> v
  | e :: e_list -> sum (oplus v e) e_list
let ignore e = Oapp(operator "ignore", [e])
let snd e = Oapp(operator "snd", [e])

let for_loop i e1 e2 body = Ofor(true, i, e1, e2, body)

let if_then ec body = Oif(ec, body)

(* arrays in which states are stored *)
let cvec  = Ident.fresh "cvec" (* vector of positions *)
let dvec  = Ident.fresh "dvec" (* vector of derivatives *)
let zin_vec  = Ident.fresh "zin_vec" (* the in vector of boolean. *)
                                     (* [zin_vec.(i) = true] means that *)
                                     (* [zout_vec.(i)] has a zero-crossing *)
let zout_vec  = Ident.fresh "zout_vec" (* the out vector of zero-crossings *)
let cstart    = Ident.fresh "cstart"   (* begining in the cvector *)
let zstart    = Ident.fresh "zstart"   (* begining in the zvector *)
let output    = Ident.fresh "output"   (* the output of the function *)

(* access functions for state vectors *)

(* First solution: functions are defined in module [ZLS] *)
let solver_fn n  =
  Oglobal(Lident.Modname { Lident.qual = "Zls"; Lident.id = n })

(* create accessor and mutator functions for state vectors *)
let make_get get_fn array_ident idx =
  Oapp(get_fn, [Olocal(array_ident); idx])

let make_set set_fn array_ident idx e =
  Oapp(set_fn, [Olocal(array_ident); idx; e])

let get cvec e = make_get (solver_fn "get") cvec e
let set cvec idx e = make_set (solver_fn "set") cvec idx e
let get cvec e = make_get (solver_fn "get_zin") cvec e

(* Second solution (default): direct access to arrays *)
let get cvec e = Oindex(Olocal(cvec), e)
let set cvec idx e = Oassign(Oleft_index(Oleft_name(cvec), idx), e)
let get_zin zvec e = oneq (Oindex(Olocal(zvec), e)) int32_0
let rec letin p_e_list i =
  match p_e_list with
  | [] -> i
  | (p, e) :: p_e_list -> Olet(p, e, letin p_e_list i)
					   
(** Compute the index associated to a state variable [x] in the current block *)
(* [build_index m_list = (ctable, csize), (ztable, zsize), m_list] *)
let build_index m_list =
  (* build two tables. The table [ctable] associates an integer index to *)
  (* every continuous state variable; [ztable] do the same for zero-crossings *)
  (* also return the size of every table *)
  let build ((ctable, csize), (ztable, zsize))
	    { m_name = n; m_kind = m; m_value = e_opt } = 
    match m with
    | None -> (ctable, csize), (ztable, zsize)
    | Some(k) ->
       match k with
       | Horizon | Period | Encore -> (ctable, csize), (ztable, zsize)
       | Zero -> (ctable, csize), (Env.add n zsize ztable, zsize + 1)
       | Cont -> (Env.add n csize ctable, csize + 1), (ztable, zsize) in
  let (ctable, csize), (ztable, zsize) =
    List.fold_left build ((Env.empty, 0), (Env.empty, 0)) m_list in
  (ctable, csize), (ztable, zsize)

(* Add a new method [maxsize () = ...] which returns a pair of two integers *)
(* The first is the maximum vector size for continuous states; the second for *)
(* zero-crossings. *)
let maxsize csize zsize instances =
  (* the main function is of the form:
     let c1, z1 = o1.maxsize () in ... in let cn, cn = on.maxsize () in
     c1 + ... + cn, z1 + ... + zn *)
  let one (c_list, z_list, p_e_list)
	  { i_name = o; i_machine = ei; i_kind = k } =
    match k with
    | Tcont ->
       let r1 = Ident.fresh "r" in
       let r2 = Ident.fresh "r" in
       (local r1) :: c_list,
       (local r2) :: z_list,
       (tuplepat [varpat r1 Initial.typ_int; varpat r2 Initial.typ_int],
        Omethodcall { met_machine = None; met_name = Omaxsize;
                      met_instance = Some(o, []); met_args = [] }) :: p_e_list
    | _ -> c_list, z_list, p_e_list in
  let c_list, z_list, p_e_list = List.fold_left one ([], [], []) instances in
  let c = sum (int_const csize) c_list in
  let z = sum (int_const zsize) z_list in
  let e = 
    match p_e_list with 
    | [] -> Oexp (Otuple [c; z])
    | _ -> letin p_e_list (Oexp (Otuple([c; z]))) in
  { me_name = Omaxsize; me_params = []; me_body = e }

(** Add a method [horizon] which returns the next horizon. When it returns *)
(* 0.0, this means that an extra discrete step must be performed *)
(* [h] is the unique variable with kind [horizon] *)
(* if absent, horizon returns infinity *)
(* method horizon =                                          *)
(*  let v = min h (min o_1.horizon (min ... o_n.horizon)) in *)
(*  h <- infinity;                                           *)
(*  v                                                        *)
let horizon m_list instances =
  (* build the expression [min ...] *)
  let add acc { i_name = o; i_machine = ei; i_kind = k } =
       match k with
       | Tcont -> omin (call o Ohorizon []) acc
       | _ -> acc in
  (* find the horizon *)
  let find h_opt { m_name = n; m_kind = k_opt } =
    match k_opt, h_opt with
    | Some(Horizon), None -> Some(n)
    | Some(Horizon), Some _ ->
       Misc.internal_error "Inout: two horizon" Printer.name n
    | _ -> h_opt in
  let h_opt = List.fold_left find None m_list in
  let v = Ident.fresh "v" in
  let c =
    match h_opt with
    | None -> Oexp(List.fold_left add infinity instances)
    | Some(h) ->
       Olet(varpat v Initial.typ_float, List.fold_left add (state h) instances,
	   Osequence [oassign_state h infinity; Oexp(Olocal(v))]) in
  { me_name = Ohorizon; me_params = []; me_body = c }
  
(** Add a method to copy back and forth the internal representation *)
(** of the continuous state vector to the external flat representation *)
(* This function is generic: [table, size] contains the association table *)
(* [name, index] with size [size]. [assign n index] does the copy for *)
(* local memories. *)
let inout (table, size) method_name assign start (vec, ty) instances =
  (* For every input (n, index) from [table] *)
  (* run [assign n table] *)
  let add n index acc = (assign n index) :: acc in
  let c_list = Env.fold add table [] in
  (* for every instance [o] add *)
  (* [let start = call o vec start] *)
  let add acc { i_name = o; i_machine = ei; i_kind = k } =
    match k with
    | Tcont -> Olet(varpat start Initial.typ_int,
		   call o method_name [local vec; local start], acc)
    | _ -> acc in
  let c = List.fold_left add (Oexp(Olocal(start))) instances in
  (* add [let cstart = cstart + size] *)
  let c = 
    match size with
    | 0 -> c
    | _ -> Olet(varpat start Initial.typ_int, oplus (local start)
						    (int_const size), c) in
  { me_name = method_name;
    me_params = [varpat vec (Initial.typ_array ty);
		 varpat start Initial.typ_int];
    me_body = Osequence (c_list @ [c]) } 

(** Add a method to recursively apply a method to all instances *)
(* This function is generic: [table, size] contains the association table *)
(* [name, index] with size [size]. [assign n index] sets the local memories. *)
let inout_const (table, size) method_name set instances =
  (* For every input (n, index) from [table] *)
  (* run [set n table] *)
  let add n index acc = (set n index) :: acc in
  let c_list = Env.fold add table [] in
  (* for every instance [o:f] add *)
  let rec add acc insts =
    match insts with
    | [] -> acc
    | { i_name = o; i_machine = ei; i_kind = Tcont } :: insts ->
       add (Oexp(call o method_name []) :: acc) insts
    | _ :: insts -> add acc insts in
  { me_name = method_name; me_params = [];
    me_body = Osequence (add c_list instances) } 

(* Add a method cin cvec cstart = cstart' which copies [cvec] *)
(* from position [cstart] to the internal state and returns the new position *)
let cin (ctable, csize) instances =
  let assign n index =
    Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), 
                                               Ocont),
                  get cvec (oplus (local cstart) 
				  (Oconst(Oint(index))))) in
  inout (ctable, csize) Ocin assign cstart (cvec, Initial.typ_float) instances

(* Add a method cout cvec cstart = cstart' which copies the internal *)
(* continuous state into [cvec] from position [cstart]. Returns *)
(* the new position *)
let cout (ctable, csize) instances =
  let assign n index =
    Oassign(Oleft_index(Oleft_name(cvec),
                        oplus (local cstart) 
                              (Oconst(Oint(index)))),
            Ostate(Oleft_state_primitive_access(Oleft_state_name(n),
                                                Ocont))) in
  inout (ctable, csize) Ocout assign cstart (cvec, Initial.typ_float) instances
	
(* Add a method dout cvec cstart = cstart' which copies the internal *)
(* derivative into [dvec] from position [cstart]. Returns the new position *)
let dout (ctable, csize) instances =
  let assign n index =
    Oassign(Oleft_index(Oleft_name(cvec),
                        oplus (local cstart) 
                              (Oconst(Oint(index)))),
            Ostate(Oleft_state_primitive_access(Oleft_state_name(n),
                                                Oder))) in
  inout (ctable, csize) Odout assign cstart (cvec, Initial.typ_float) instances
	
(* Add a method zin zin_vec zstart = zstart' which copies [zin_vec] *)
(* from position [zstart] to the internal state and returns the new position *)
let zin (ztable, zsize) instances =
  let assign n index =
    Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), 
                                               Ozero_in),
                  get_zin zin_vec (oplus (local zstart) 
					 (Oconst(Oint(index))))) in
  inout (ztable, zsize)
	Ozin assign zstart (zin_vec, Initial.typ_int32) instances

(* Add a method clear_zin zstart = zstart' which sets the internal state for *)
(* zero-crossings to false from position [zstart]. *)
let clear_zin (ztable, zsize) instances =
  let set n _ =
    Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), 
                                               Ozero_in), bool false) in
  inout_const (ztable, zsize) Oclear_zin set instances
	      
(* Add a method cout cvec cstart = cstart' which copies the internal *)
(* continuous state into [cvec] from position [cstart]. Returns *)
(* the new position *)
let zout (ztable, zsize) instances =
  let assign n index =
    Oassign(Oleft_index(Oleft_name(zout_vec),
                        oplus (local zstart) 
                              (Oconst(Oint(index)))),
            Ostate(Oleft_state_primitive_access(Oleft_state_name(n),
                                                Ozero_out))) in
  inout
    (ztable, zsize) Ozout assign zstart (zout_vec, Initial.typ_float) instances
	
(* Add a method dzero dvec cstart = cstart' which resets to 0 the internal *)
(* derivatives in [dvec] from position [cstart]. Returns the new position *)
let dzero (ctable, csize) instances =
  let set n _ =
    Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), 
                                               Oder), float_const 0.0) in
  inout_const (ctable, csize) Odzero set instances

(** Translate a continuous-time machine *)
let machine f ({ ma_memories = m_list; ma_instances = instances;
                 ma_methods = method_list } as mach) =
  (* first associate an integer index to every continuous state *)
  (* variable or zero-crossing *)
  let (ctable, csize), (ztable, zsize) = build_index m_list in
  (* add the method maxsize *)
  let method_list = maxsize csize zsize instances :: method_list in
  (* add the methods cin, cout, zin, zout *)
  let method_list = cin (ctable, csize) instances :: method_list in
  let method_list = cout (ctable, csize) instances :: method_list in
  let method_list = dout (ctable, csize) instances :: method_list in
  let method_list = zin (ztable, zsize) instances :: method_list in
  let method_list = clear_zin (ztable, zsize) instances :: method_list in
  let method_list = dzero (ctable, csize) instances :: method_list in
  let method_list = zout (ztable, zsize) instances :: method_list in
  let method_list = horizon m_list instances :: method_list in
  { mach with ma_memories = m_list; ma_methods = method_list }

(** The main entry. Add new methods to copy the continuous state vector *)
(** back and forth into the internal state *)
let implementation impl =
  match impl with
  | Oletmachine(f, ({ ma_kind = Deftypes.Tcont } as mach)) -> 
     (* only continuous machines are concerned *)
     Oletmachine(f, machine f mach)
  | Oletmachine _ | Oletvalue _ | Oletfun _ | Oopen _ | Otypedecl _ -> impl
  
(* Simulate a continuous system [f]. If [f] is a continuous machine *)
(* define a new machine where the vector of derivatives is blanked *)
(* system f_sim is
     memory mcsize = 0; mzsize = 0;
     instance o: f
     method step cvec dvec zin_vec t = 
       ignore (o.cin cvec 0);
       ignore (o.zin zin_vec 0);
       let output = o.step t in
       o.clear_zin;
       o.dzero;
       ignore (o.cout cvec 0);
       output
     method derivative cvec dvec t =
       ignore (o.cin cvec 0);
       ignore (o.step t);
       ignore (o.dout dvec 0)
     method crossings cvec zout_vec t =
       ignore (o.cin cvec 0);
       ignore (o.step t);
       ignore (o.zout zout_vec 0)
     method reset = o.reset 
     method maxsize = 
       let csize, zsize = o.maxsize in
       mcsize := csize; mzsize := zsize;
       (csize, zsize)
     method csize = mcsize
     method zsize = mzsize  
     method horizon = o.horizon   
   end *)

let simulate f =
  let o = Ident.fresh "" in
  let time = Ident.fresh "t" in
  let csize = Ident.fresh "csize" in
  let zsize = Ident.fresh "zsize" in
  let mcsize = Ident.fresh "mcsize" in
  let mzsize = Ident.fresh "mzsize" in
  let call m_name e_list = call o m_name e_list in
  { ma_kind = Deftypes.Tcont;
    ma_params = [];
    ma_memories = [{ m_name = mcsize;
		     m_value = Some(int_const 0);
		     m_typ = Initial.typ_int;
		     m_kind = None;
		     m_size = [] };
		   { m_name = mzsize;
		     m_value = Some(int_const 0);
		     m_typ = Initial.typ_int;
		     m_kind = None;
		     m_size = [] }];
    ma_instances = [{ i_name = o;
		      i_machine = Oglobal(f);
		      i_kind = Deftypes.Tcont;
		      i_params = [];
		      i_size = [] }];
    ma_methods = 
      [{ me_name = Ostep;
         me_params =
	   [varpat cvec (Initial.typ_array Initial.typ_float);
	    varpat dvec (Initial.typ_array Initial.typ_float);
	    varpat zin_vec (Initial.typ_array Initial.typ_int32);
	    varpat time Initial.typ_float];
         me_body =
           olets [Owildpat, call Ocin [local cvec; int_const 0];
		  Owildpat, call Ozin [local zin_vec; int_const 0];
		  Owildpat, call Ostep [tuple [local time; void]];
		  Owildpat, call Oclear_zin [];
		  Owildpat, call Odzero [];
		  Owildpat, call Ocout [local cvec; int_const 0]]
		 (Oexp(Oconst(Ovoid))) };
       { me_name = Oderivatives;
         me_params =
	   [varpat cvec (Initial.typ_array Initial.typ_float);
	    varpat dvec (Initial.typ_array Initial.typ_float);
	    varpat time Initial.typ_float];
         me_body = 
           olets [Owildpat, call Ocin [local cvec; int_const 0];
		  Owildpat, call Ostep [tuple [local time; void]];
		  Owildpat, call Odout [local dvec; int_const 0]]
	 	 (Oexp(Oconst(Ovoid))) };
       { me_name = Ocrossings;
         me_params =
	   [varpat cvec (Initial.typ_array Initial.typ_float);
	    varpat zout_vec (Initial.typ_array Initial.typ_float);
	    varpat time Initial.typ_float];
         me_body = 
           olets [Owildpat, call Ocin [local cvec; int_const 0];
		  Owildpat, call Ostep [tuple [local time; void]];
		  Owildpat, call Ozout [local zout_vec; int_const 0]]
		 (Oexp(Oconst(Ovoid))) };
       { me_name = Oreset;
         me_params =
	   [varpat cvec (Initial.typ_array Initial.typ_float)];
         me_body = olets [Owildpat, call Oreset [];
			  Owildpat, call Ocout [local cvec; int_const 0]]
			 (Oexp(Oconst(Ovoid))) };
       { me_name = Omaxsize; 
         me_params = [];
	 me_body = 
	   olets [tuplepat [varpat csize Initial.typ_int;
			    varpat zsize Initial.typ_int], call Omaxsize []]
		 (Osequence
		    [oassign_state mcsize (local csize); 
		     oassign_state mzsize (local zsize);
		     Oexp(tuple [local csize; local zsize])]) };
       { me_name = Ocsize;
         me_params = []; me_body = Oexp(Ostate(Oleft_state_name(mcsize))) };
       { me_name = Ozsize;
         me_params = []; me_body = Oexp (Ostate(Oleft_state_name(mzsize))) };
       { me_name = Ohorizon;
	 me_params = []; me_body = Oexp(call Ohorizon []) } ] }
        
let implementation_list impl_list = Misc.iter implementation impl_list
