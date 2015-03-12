(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2014                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* Represents the continuous state by vectors *)
(* A machine with continuous states take vectors as input *)
(* machine m =                         *)
(*    memories (k_i m_k: t_i)_{i in I} *)
(*    instance (j_i: f_i)_{i in J}     *)
(*    method cont pat = e1             *)
(*    method step pat = e2             *)
(*    method reset = e                 *)
(*                                     *)
(* machine m =                         *)
(*    memories (k_i m_k : t_i)_{i in I'}  I' subseteq I. *)
(*             -- remove continuous states and zeros from I  *)
(*             cstart: int = 0 -- starting position of the cvector *)
(*             zstat: int = 0 -- starting position of the zvector *)
(*             cstate: cont = empty the representation of the continuous state *)
(*                                  this one is shared among all machines *)
(*    instance (j_i: f_i)_{i in J} *)
(*    method init p = e -- initialization. This function must be executed first *)
(*    method derivatives p = e1                                                *)
(*                    -- sets derivatives and copies of continuous state vars. *)
(*                    -- it is called by the numerical solver *)
(*    method crossings p = e1                                                *)
(*                    -- sets the zero-crossing vector. *)
(*                    -- it is called by the numerical solver *)
(*    method step p = e2 -- main step function *)
(*    method encore = e -- a boolean telling that an extra iteration is necessary *)
(*    method reinit = e -- do we have to re-initialize the solver *)
(*    method reset = e -- resets the discrete state *)
(*    method maxsize = e -- returns the max length of the cvector and zvector *)

open Misc
open Ident
open Lident
open Deftypes
open Obc
open Format

let wildpat = make (Owildpat)
let void = make (Oconst(Ovoid))
let varpat x = make (Ovarpat(x))
let tuplepat p_list = make (Otuplepat(p_list))
let tuple e_list = make (Otuple(e_list))
let var x = make (Olocal(x, false))
let statevar x = make (Ostate(Oleft_state_name(x)))
let int_const v = make (Oconst(Oint(v)))
let float_const v = make (Oconst(Ofloat(v)))
let app op l = make (Oapp(op, l))
let global n = make (Oglobal(n))
let plus e1 e2 = make (Oapp(Modname { qual = "Pervasives"; id = "(+)" }, [e1; e2]))
let max e1 e2 = make (Oapp(Modname { qual = "Pervasives"; id = "max" }, [e1; e2]))
let rec op_list op e_list =
  match e_list with
  | [] -> int_const 0
  | [e] -> e
  | e :: e_list -> op e (op_list op e_list)
let rec sequence e_list =
  match e_list with
  | [] -> make (Oconst(Ovoid))
  | [e] -> e
  | e :: e_list -> make (Osequence(e, sequence e_list))
let for_loop i e1 e2 body =
  make (Ofor(true, i, e1, e2, body))

(* access functions are defined in module [ZLS] *)
let solver_fn n  = Lident.Modname { Lident.qual = "Zls"; Lident.id = n }

(* create accessor and mutator functions for states vectors *)
let make_get get_fn array_ident idx =
  Oapp(get_fn, [make (Olocal (array_ident, false)); idx])

let make_set set_fn array_ident idx e =
  Oapp(set_fn, [make (Olocal (array_ident, false)); idx; e])

(* arrays in which states are stored *)
let cvector  = Ident.fresh "cvector" (* continuous state vector *)
let cstart = Ident.fresh "cstart" (* begining in the cvector *)
let state_cstart = Ident.fresh "cstart" (* the same stored in the internal state *)
let zstart = Ident.fresh "zstart" (* begining in the zvector *)
let state_zstart = Ident.fresh "zstart" (* the same in the internal state *)
let time = Ident.fresh "time" (* the current time *)

let extra_pat = varpat cvector
let extra_arg = var cvector

let zget e = make_get (solver_fn "zget") cvector e
let zset idx e = make_set (solver_fn "zset") cvector idx e
let cget e = make_get (solver_fn "cget") cvector e
let cset idx e = make_set (solver_fn "cset") cvector idx e
let dset idx e = make_set (solver_fn "dset") cvector idx e
let set_final idx e1 e2 = make (Oapp(solver_fn "set_final", [idx; e1; e2]))
let get_final e = make (Oapp(solver_fn "get_final", [e]))

(** Compute the index associated to a state variable [x] in the current block *)
(* [build_index m_list = (ctable, csize), (ztable, zsize), m_list] *)
let build_index m_list =
  (* build two tables. The table [ctable] associates an integer index to *)
  (* every continuous state variable; [ztable] do the same for zero-crossings *)
  (* also return the size of every table and a new set of memories *)
  (* in which two entries [state_cstate] and [state_zstate] are added *)
  let build 
	((ctable, csize), (ztable, zsize), m_list) 
	((n, (mem, ty, e_opt)) as entry) =
    match mem with
    | Discrete -> (ctable, csize), (ztable, zsize), entry :: m_list
    | Zero -> 
       (* remove the variable from the list of memories *)
       (ctable, csize), (Env.add n zsize ztable, zsize + 1), m_list
    | Cont -> 
       (* remove the variable from the list of memories *)
       (Env.add n csize ctable, csize + 1), (ztable, zsize), m_list in
  let (ctable, csize), (ztable, zsize), m_list =
    List.fold_left build ((Env.empty, 0), (Env.empty, 0), []) m_list in
  let m_list =
    (state_cstart, (Discrete, Initial.typ_int, Some(int_const 0))) ::
      (state_zstart, (Discrete, Initial.typ_int, Some(int_const 0))) :: m_list in
  (ctable, csize), (ztable, zsize), m_list

(* Compile an expression [exp env ztable ctable e] rewrites [e] into *)
(* a new expression in which reads/writes to state variables are changed *)
(* [env] is the environment of instances *)
let exp env (ctable, csize) (ztable, zsize) e =
  let rec exp ({ desc = desc } as e) =
    let desc = match desc with
      | Oconst _ | Oconstr0 _ | Oglobal _ | Olocal _ -> desc
      | Oconstr1(c, e_list) -> Oconstr1(c, List.map exp e_list)
      | Ostate(Oleft_state_primitive_access(Oleft_state_name(n), Ocontinuous)) ->
	 (* [x.cont] into [cget (cstart + index x)] *)
	 cget (plus (var cstart) (make (Oconst(Oint(Env.find n ctable)))))
      | Ostate(Oleft_state_primitive_access(Oleft_state_name(n), Ozero_in)) ->
	 (* [x.zin] into [zget (zstart + index x)] *)
	 zget (plus (var zstart) (make (Oconst(Oint(Env.find n ztable)))))
      | Ostate _ -> desc
      | Oindex(e1, e2) -> Oindex(exp e1, exp e2)
      | Otuple(e_list) -> Otuple(List.map exp e_list)
      | Oapp(f, e_list) -> Oapp(f, List.map exp e_list)
      | Omethod({ c_method_name; c_instance = o_opt } as m, e_list) -> 
	 (* turn a method call o.f(e) into o.f(cvector, e) *)
	 let modify = 
	   match o_opt with 
	     | None -> true 
	     | Some(o) -> 
	         let _, k = try Env.find o env with Not_found -> assert false in
	         match k with Deftypes.Tcont -> true | _ -> false in
	 let e_list = List.map exp e_list in
	 let e_list = if modify then extra_arg :: e_list else e_list in
	 Omethod(m, e_list)
      | Orecord(l_e_list) -> 
	 Orecord(List.map (fun (l, e) -> (l, exp e)) l_e_list)
      | Orecord_access(e, label) -> Orecord_access(exp e, label)
      | Otypeconstraint(e, ty_e) -> Otypeconstraint(exp e, ty_e)
      | Olet(p_e_list, e) ->
	 Olet(List.map (fun (p, e) -> (p, exp e)) p_e_list, exp e)
      | Oletvar(x, ty, e_opt, e) ->
	 Oletvar(x, ty, Misc.optional_map exp e_opt, exp e)
      | Oifthenelse(e1, e2, e3) -> Oifthenelse(exp e1, exp e2, exp e3)
      | Ofor(b, x, e1, e2, e) -> Ofor(b, x, exp e1, exp e2, exp e)
      | Omatch(e, m_e_list) ->
	 Omatch(exp e, 
		List.map (fun { w_pat = p; w_body = e } -> 
			  { w_pat = p; w_body = exp e }) m_e_list)
      | Oassign(left, e) -> Oassign(left, exp e)
      | Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), 
						   Ocontinuous), e) ->
	 (* [x.cont <- e] into [cset (cstart + index x) x] *)
	 cset (plus (var cstart) 
		    (make (Oconst(Oint(Env.find n ctable)))))
	      (exp e)
      | Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), 
						   Oderivative), e) ->
	 (* [x.der <- e] into [dset (cstart + index x) e] *)
	 dset (plus (var cstart) (make (Oconst(Oint(Env.find n ctable))))) 
	      (exp e)
      | Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), Ozero_out),
		      e) ->
	 (* [x.zout <- e] into [zset (cstart + index x) e] *)
	 zset (plus (var zstart) (make (Oconst(Oint(Env.find n ztable)))))
	      (exp e)
      | Oassign_state(left_state, e) -> Oassign_state(left_state, exp e)  
      | Osequence(e1, e2) -> Osequence(exp e1, exp e2) in
    { e with desc = desc } in
  exp e

(* Prelude to be added for the [step] method *)
let prelude_step csize zsize e =
  (* add a prelude *)
  (* [let cstart = cvec.final and zstart = zvec_in.final in
      let c = cstart + csize and z = zstart + zsize in
      cvec.final <- c; zvec_in.final <- z; zvec_out.final <- z;
      self.cstart <- cstart; self.zstart <- zstart;
      ...] *)
  let c = Ident.fresh "c" and z = Ident.fresh "z" in
  make (Olet([tuplepat [varpat cstart; varpat zstart], get_final (var cvector)],
	     make (Olet([varpat c, plus (var cstart) (int_const csize);
			 varpat z, plus (var zstart) (int_const zsize)],
			sequence 
			  [set_final (var cvector) (var c) (var z);
			   make (Oassign_state(Oleft_state_name(state_cstart),
					       var cstart));
			   make (Oassign_state(Oleft_state_name(state_zstart),
					       var zstart));
			   e]))))

(* Prelude to be added for the [cont] method *)
let prelude csize zsize e =
  (* add a prelude *)
  (* [let cstart = self.cstart and zstart = self.zstart in ...] *)
  make (Olet([varpat cstart, make (Ostate(Oleft_state_name(state_cstart)));
	      varpat zstart, make (Ostate(Oleft_state_name(state_zstart)))],
	     e))

(* Add a new method [maxsize () = ...] which returns a pair of two integers *)
(* The first is the maximum vector size for continuous states; the second for *)
(* zero-crossings *)
let maxsize_method csize zsize e =
  (* neutral value *)
  let zero = make (Otuple [int_const 0; int_const 0]) in
  let current = make (Otuple [int_const csize; int_const zsize]) in
  (* combine all results. First remove neutral values *)
  let op_list op e_list =
    let e_list = List.filter (fun x -> not (x = zero)) e_list in
    match e_list with
      | [] -> zero
      | [e] -> e
      | _ ->
	let r_p_e_list = 
	  List.map 
	    (fun e -> let r1 = Ident.fresh "r" in
		      let r2 = Ident.fresh "r" in
		      ((var r1, var r2), 
		       (tuplepat [varpat r1; varpat r2], e))) e_list in
	let r_list, p_e_list = List.split r_p_e_list in
	let r1_list, r2_list = List.split r_list in
	make (Olet(p_e_list, tuple [op_list op r1_list; op_list op r2_list])) in

  (* the main function *)
  let rec maxsize ({ desc = desc } as e) =
    match desc with
    | Oconst _ | Oconstr0 _ | Oglobal _ | Olocal _ | Ostate _ -> zero
    | Oconstr1(_, e_list) | Otuple(e_list) | Oapp(_, e_list) -> 
        let m_list = List.map maxsize e_list in
	op_list plus m_list
    | Oindex(e1, e2) -> op_list plus [maxsize e1; maxsize e2]
    | Omethod(mc, e_list) -> 
      let m_list = List.map maxsize e_list in
      let m_list = 
	{ e with desc = Omethod({ mc with c_method_name = Omaxsize }, []) } 
	:: m_list in
      op_list plus m_list
  | Orecord(l_e_list) -> 
     let m_list = List.map (fun (_, e) -> maxsize e) l_e_list in
     op_list plus m_list
  | Orecord_access(e, _) | Otypeconstraint (e, _) 
  | Oletvar(_, _, None, e) | Oassign(_, e) | Oassign_state(_, e) -> maxsize e
  | Olet(p_e_list, e) ->
     op_list plus (maxsize e :: (List.map (fun (_, e) -> maxsize e) p_e_list))
  | Oletvar(_, _, Some(e1), e2) 
  | Osequence(e1, e2) -> op_list plus [maxsize e1; maxsize e2]
  | Oifthenelse(e1, e2, e3) -> 
     op_list plus [maxsize e1; op_list max [maxsize e2; maxsize e3]]
  | Ofor(_, _, e1, e2, e3) -> 
     op_list plus [maxsize e1; maxsize e2; maxsize e3]
  | Omatch(e, m_h_list) ->
     op_list plus 
	     [maxsize e;
	      op_list max (List.map (fun { w_body = e } -> maxsize e) m_h_list)] in
  let e = op_list plus [current; maxsize e] in
  { m_name = Omaxsize;
    m_param = [];
    m_body = e } 

(** Translate a continuous-time machine *)
let machine f ({ m_memories = m_list; m_instances = instances;
	       m_methods = method_list } as mach) =
  (* first associate an integer index to every continuous state *)
  (* variable or zero-crossing *)
  let (ctable, csize), (ztable, zsize), m_list = build_index m_list in
  (* produces the environment of instances *)
  let env =
    List.fold_left 
      (fun acc (o, f, k) -> Env.add o (f, k) acc) Env.empty instances in
  let one_method acc 
		 ({ m_name = m_name; m_param = pat_list; m_body = e } as entry) =
    let pat_list = extra_pat :: pat_list in
    match m_name with
    | Ostep ->
       (* first compute the size for cvectors and zvectors *)
       let maxsize_method = maxsize_method csize zsize e in
       let e = exp env (ctable, csize) (ztable, zsize) e in
       let e = prelude_step csize zsize e in
       (* adds a method [derivatives] and [crossings] *)
       maxsize_method ::
	 { entry with m_param = pat_list; m_body = e } :: acc
    | _ -> 
       let e = exp env (ctable, csize) (ztable, zsize) e in
       let e = prelude csize zsize e in
       { entry with m_param = pat_list; m_body = e } :: acc in
  { mach with m_memories = m_list; 
    m_methods = List.fold_left one_method [] method_list }

let implementation impl =
  match impl.desc with
  | Oletmachine(f, ({ m_kind = Deftypes.Tcont } as mach)) -> 
     (* only continuous machines are concerned *)
     { impl with desc = Oletmachine(f, machine f mach) }
  | Oletmachine _ | Oletvalue _ | Oletfun _ | Oopen _ | Otypedecl _ -> impl
  
(* Simulate a continuous system [f]. If [f] is a continuous machine *)
(* define a new machine where the vector of derivatives is blanked *)
(* system f_sim is
     instance o: f
     method step cvector t = 
       let cstart, zstart = get_final cvector in
       for i = 0 to cstart - 1 do dset cvector i 0.0;
       set_final cvector 0 0;
       let _, t = o.step cvector t in t
     method derivative cvector t = let _ = o.step cvector t in ()
     method maxsize = o.maxsize
     method crossings cvector t = let _ = o.step cvector t in ()
     method reset cvector = o.reset cvector
   end *)

let simulate f =
  let o = Ident.fresh "" in
  let call m_name e_list = 
    make (Omethod({ c_machine = f; c_method_name = m_name; 
		    c_instance = Some(o) }, e_list)) in
  { m_kind = Deftypes.Tcont;
    m_memories = [];
    m_instances = [o, f, Deftypes.Tcont];
    m_methods = 
      [{ m_name = Ostep;
	 m_param = [varpat cvector; varpat time];
	 m_body =
	  make (Olet([tuplepat [varpat cstart; varpat zstart], 
		      get_final (var cvector)],
		     let i = Ident.fresh "" in
		     let h = Ident.fresh "" in
		     sequence
		       [for_loop i (int_const 0) (plus (var cstart)
						    (int_const (-1)))
			   (make (dset (var i) (float_const 0.0)));
			set_final (var cvector) (int_const 0) (int_const 0);
			make (Olet([
                          tuplepat [wildpat; varpat h],
                          call Ostep [var cvector; var time; void]], var h))])) };
       { m_name = Oderivatives;
	 m_param = [varpat cvector; varpat time];
	 m_body = 
	   make (Olet([wildpat, call Ostep [var cvector; var time]], void)) };
       { m_name = Omaxsize; 
	 m_param = []; 
	 m_body = call Omaxsize [] };
       { m_name = Ocrossings;
	 m_param = [varpat cvector; varpat time];
	 m_body = 
	   make (Olet([wildpat, call Ostep [var cvector; var time]], void)) };
       { m_name = Oreset;
	 m_param = [varpat cvector];
	 m_body = call Oreset [var cvector] }] }
	  		       
let implementation_list impl_list = Misc.iter implementation impl_list
