(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2015                                               *)
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
(*    method clear_zin start : int -- sets the internal zero-crossings to false *)
(*    method zout zoutvec start: int -- copies the internal state into zoutvec *)

open Misc
open Ident
open Lident
open Deftypes
open Obc
open Format

let varpat x = make (Ovarpat(x))
let tuplepat p_list = make (Otuplepat(p_list))
let wildpat = make (Owildpat)
let void = make (Oconst(Ovoid))
let int32_0 = make (Oconst(Oint32 0))
let tuple e_list = make (Otuple(e_list))
let var x = make (Olocal(x, false))
let shared x = make (Olocal(x, true))
let int_const v = make (Oconst(Oint(v)))
let float_const v = make (Oconst(Ofloat(v)))
let bool b = make (Oconst(Obool(b)))
let plus e1 e2 = 
  make (Oapp(Modname (Initial.pervasives_name "(+)"), [e1; e2]))
let lte e1 e2 = 
  make (Oapp(Modname (Initial.pervasives_name "(<=)"), [e1; e2]))
let lt e1 e2 = 
  make (Oapp(Modname (Initial.pervasives_name "(<)"), [e1; e2]))
let neq e1 e2 = 
  make (Oapp(Modname (Initial.pervasives_name "(<>)"), [e1; e2]))
let onot e = make (Oapp(Modname (Initial.pervasives_name "not"), [e]))
let oand e1 e2 = make (Oapp(Modname (Initial.pervasives_name "(&&)"), [e1; e2]))
let oassign id e = make (Oassign(Oleft_name(id), e))
let oassign_state id e = make (Oassign_state(Oleft_state_name(id), e))
let oletvar id ty e_opt e = make (Oletvar(id, ty, e_opt, e))
let owhile e1 e2 = make (Owhile(e1, e2))
let call o f m_name e_list = 
  make (Omethod({ c_machine = f; c_method_name = m_name; c_instance = Some(o) }, 
                e_list))
let olet p e1 e2 = make (Olet([p, e1], e2))
let rec sum v e_list =
  match e_list with
  | [] -> v
  | e :: e_list -> sum (plus v e) e_list
let rec sequence e_list =
  match e_list with
  | [] -> void
  | [e] -> e
  | e :: e_list -> make (Osequence(e, sequence e_list))
let ignore e = make (Oapp(Modname (Initial.pervasives_name "ignore"), [e]))
let snd e = make (Oapp(Modname (Initial.pervasives_name "snd"), [e]))

let for_loop i e1 e2 body =
  make (Ofor(true, i, e1, e2, body))

let if_then ec cmd =
  make (Oifthenelse (ec, cmd, void))

(* arrays in which states are stored *)
let cvec  = Ident.fresh "cvec" (* vector of positions *)
let dvec  = Ident.fresh "dvec" (* vector of derivatives *)
let zin_vec  = Ident.fresh "zin_vec" (* the in vector of boolean. *)
                                     (* [zin_vec.(i) = true] means that *)
                                     (* [zout_vec.(i)] has a zero-crossing *)
let zout_vec  = Ident.fresh "zout_vec" (* the out vector of zero-crossings *)
let cstart    = Ident.fresh "cstart"   (* begining in the cvector *)
let zstart    = Ident.fresh "zstart"   (* begining in the zvector *)
let horizon   = Ident.fresh "horizon"  (* the current horizon *)
let output    = Ident.fresh "output"   (* the output of the function *)

(* access functions for state vectors *)

(* First solution: functions are defined in module [ZLS] *)
let solver_fn n  = Lident.Modname { Lident.qual = "Zls"; Lident.id = n }

(* create accessor and mutator functions for state vectors *)
let make_get get_fn array_ident idx =
  make (Oapp(get_fn, [make (Olocal (array_ident, false)); idx]))

let make_set set_fn array_ident idx e =
  make (Oapp(set_fn, [make (Olocal (array_ident, false)); idx; e]))

let get cvec e = make_get (solver_fn "get") cvec e
let set cvec idx e = make_set (solver_fn "set") cvec idx e
let get cvec e = make_get (solver_fn "get_zin") cvec e

(* Second solution (default): direct access to arrays *)
let get cvec e = make (Oindex(make (Olocal(cvec, false)), e))
let set cvec idx e = make (Oassign(Oleft_index(Oleft_name(cvec), idx), e))
let get_zin zvec e = neq (make (Oindex(make (Olocal(zvec, false)), e))) int32_0

(** Compute the index associated to a state variable [x] in the current block *)
(* [build_index m_list = (ctable, csize), (ztable, zsize), m_list] *)
let build_index m_list =
  (* build two tables. The table [ctable] associates an integer index to *)
  (* every continuous state variable; [ztable] do the same for zero-crossings *)
  (* also return the size of every table *)
  let build ((ctable, csize), (ztable, zsize)) (n, (mem, ty, e_opt)) =
    match mem with
    | Discrete -> (ctable, csize), (ztable, zsize)
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
  let one (c_list, z_list, p_e_list) (o, f, k) =
    match k with
    | Tcont ->
       let r1 = Ident.fresh "r" in
       let r2 = Ident.fresh "r" in
       (var r1) :: c_list,
       (var r2) :: z_list,
       (tuplepat [varpat r1; varpat r2],
        make (Omethod({ c_machine = f; c_method_name = Omaxsize;
                        c_instance = Some(o) }, []))) :: p_e_list
    | _ -> c_list, z_list, p_e_list in
  let c_list, z_list, p_e_list = List.fold_left one ([], [], []) instances in
  let c = sum (int_const csize) c_list in
  let z = sum (int_const zsize) z_list in
  let e = 
    match p_e_list with 
    | [] -> tuple [c; z] | _ -> make (Olet(p_e_list, tuple [c; z])) in
  { m_name = Omaxsize; m_param = []; m_body = e }

(** Add a method to copy back and forth the internal representation *)
(** of the continuous state vector to the external flat representation *)
(* This function is generic: [table, size] contains the association table *)
(* [name, index] with size [size]. [assign n index] does the copy for *)
(* local memories. *)
let inout (table, size) method_name assign start vec instances =
  (* For every input (n, index) from [table] *)
  (* run [assign n table] *)
  let add n index acc = (assign n index) :: acc in
  let c_list = Env.fold add table [] in
  (* for every instance [o:f] add *)
  (* [let start = call o f vec start] *)
  let add acc (o, f, k) =
    match k with
    | Tcont -> olet (varpat start) (call o f method_name [var vec; var start]) acc
    | _ -> acc in
  let c = List.fold_left add (var start) instances in
  (* add [let cstart = cstart + size] *)
  let c = 
    match size with
    | 0 -> c
    | _ -> olet (varpat start) (plus (var start) (int_const size)) c in
  { m_name = method_name; m_param = [varpat vec; varpat start];
    m_body = sequence (c_list @ [c]) } 

(** Add a method to reset the values of an internal representation. *)
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
    | (o, f, Tcont) :: insts -> add (call o f method_name [] :: acc) insts
    | _ :: insts -> add acc insts in
  { m_name = method_name; m_param = [];
    m_body = sequence (add c_list instances) } 
  
(* Add a method cin cvec cstart = cstart' which copies [cvec] *)
(* from position [cstart] to the internal state and returns the new position *)
let cin (ctable, csize) instances =
  let assign n index =
    make (Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), 
                                                     Ocontinuous),
                        get cvec (plus (var cstart) 
                                       (make (Oconst(Oint(index))))))) in
  inout (ctable, csize) Ocin assign cstart cvec instances

(* Add a method cout cvec cstart = cstart' which copies the internal *)
(* continuous state into [cvec] from position [cstart]. Returns the new position *)
let cout (ctable, csize) instances =
  let assign n index =
    make (Oassign(Oleft_index(Oleft_name(cvec),
                              plus (var cstart) 
                                       (make (Oconst(Oint(index))))),
                  make (Ostate(Oleft_state_primitive_access(Oleft_state_name(n),
                                                            Ocontinuous))))) in
  inout (ctable, csize) Ocout assign cstart cvec instances

(* Add a method dout cvec cstart = cstart' which copies the internal *)
(* derivative into [dvec] from position [cstart]. Returns the new position *)
let dout (ctable, csize) instances =
  let assign n index =
    make (Oassign(Oleft_index(Oleft_name(cvec),
                              plus (var cstart) 
                                       (make (Oconst(Oint(index))))),
                  make (Ostate(Oleft_state_primitive_access(Oleft_state_name(n),
                                                            Oderivative))))) in
  inout (ctable, csize) Odout assign cstart cvec instances

(* Add a method zin zin_vec zstart = zstart' which copies [zin_vec] *)
(* from position [zstart] to the internal state and returns the new position *)
let zin (ztable, zsize) instances =
  let assign n index =
    make (Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), 
                                                     Ozero_in),
                        get_zin zin_vec (plus (var zstart) 
                                       (make (Oconst(Oint(index))))))) in
  inout (ztable, zsize) Ozin assign zstart zin_vec instances

(* Add a method clear_zin zstart = zstart' which sets the internal state for *)
(* zero-crossings to false from position [zstart]. *)
let clear_zin (ztable, zsize) instances =
  let set n _ =
    make (Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), 
                                                     Ozero_in), bool false)) in
  inout_const (ztable, zsize) Oclear_zin set instances

(* Add a method cout cvec cstart = cstart' which copies the internal *)
(* continuous state into [cvec] from position [cstart]. Returns the new position *)
let zout (ztable, zsize) instances =
  let assign n index =
    make (Oassign(Oleft_index(Oleft_name(zout_vec),
                              plus (var zstart) 
                                       (make (Oconst(Oint(index))))),
                  make (Ostate(Oleft_state_primitive_access(Oleft_state_name(n),
                                                            Ozero_out))))) in
  inout (ztable, zsize) Ozout assign zstart zout_vec instances

(* TODO: Add a method dzero dvec cstart = cstart' which resets to 0 the internal *)
(* derivatives in [dvec] from position [cstart]. Returns the new position *)
let dzero (ctable, csize) instances =
  let set n _ =
    make (Oassign_state(Oleft_state_primitive_access(Oleft_state_name(n), 
                                                     Oderivative), float_const 0.0)) in
  inout_const (ctable, csize) Odzero set instances

(** Translate a continuous-time machine *)
let machine f ({ m_memories = m_list; m_instances = instances;
                 m_methods = method_list } as mach) =
  (* first associate an integer index to every continuous state *)
  (* variable or zero-crossing *)
  let (ctable, csize), (ztable, zsize) = build_index m_list in
  (* add the method maxsize *)
  let method_list = maxsize csize zsize instances :: method_list in
  (* add the methods cin, cout, zin, zout *)
  let method_list = cin (ctable, csize) instances :: method_list in
  let method_list = cout (ctable, csize) instances :: method_list in
  let method_list = dout (ctable, csize) instances :: method_list in
  let method_list = dzero (ctable, csize) instances :: method_list in
  let method_list = zin (ztable, zsize) instances :: method_list in
  let method_list = clear_zin (ztable, zsize) instances :: method_list in
  let method_list = zout (ztable, zsize) instances :: method_list in
  { mach with m_memories = m_list; m_methods = method_list }

(** The main entry. Add new methods to copy the continuous state vector *)
(** back and forth into the internal state *)
let implementation impl =
  match impl.desc with
  | Oletmachine(f, ({ m_kind = Deftypes.Tcont } as mach)) -> 
     (* only continuous machines are concerned *)
     { impl with desc = Oletmachine(f, machine f mach) }
  | Oletmachine _ | Oletvalue _ | Oletfun _ | Oopen _ | Otypedecl _ -> impl
  
(* Simulate a continuous system [f]. If [f] is a continuous machine *)
(* define a new machine where the vector of derivatives is blanked *)
(* system f_sim is
     memory mcsize = 0; mzsize = 0;
     instance o: f
     method step cvec zin_vec t = 
       var horizon = 0.0 in
       let _, h = o.step t in
       o.zin zin_vec 0;
       let _, h = o.step t in
       horizon := h;
       o.clear_zin;
       while horizon <= t do
         let _, h = o.step t in
         horizon := h;
       done;
       let csize = o.cout cvec 0 in
       for i = 0 to csize - 1 do dvec.(i) <- 0.0 done;
       horizon
     method derivative cvec dvec t =
       let _ = o.cin cvec 0 in
       let _ = o.step t in
       o.dout dvec 0; 
       ()
     method crossings cvec zout_vec t =
       let _ = o.cin cvec 0 in
       let _ = o.step t in
       o.zout zout_vec 0; ()
     method reset = o.reset 
     method maxsize = 
       let csize, zsize = o.maxsize in
       mcsize := csize; mzsize := zsize;
       (csize, zsize)
     method csize = mcsize
     method zsize = mzsize     
   end *)

let simulate f =
  let o = Ident.fresh "" in
  let t = Ident.fresh "t" in
  let csize = Ident.fresh "csize" in
  let zsize = Ident.fresh "zsize" in
  let mcsize = Ident.fresh "mcsize" in
  let mzsize = Ident.fresh "mzsize" in
  let i = Ident.fresh "i" in
  let call m_name e_list = call o f m_name e_list in
  { m_kind = Deftypes.Tcont;
    m_memories = [(mcsize, (Discrete, Initial.typ_int, Some (int_const 0)));
                  (mzsize, (Discrete, Initial.typ_int, Some (int_const 0)))];
    m_instances = [o, f, Deftypes.Tcont];
    m_methods = 
      [{ m_name = Ostep;
         m_param = [varpat cvec; varpat dvec; varpat zin_vec; varpat t];
         m_body =
           (sequence [
             ignore (call Ocin [var cvec; int_const 0]);
             ignore (call Ozin [var zin_vec; int_const 0]);
             olet (tuplepat [varpat output; varpat horizon])
                  (call Ostep [var t; void])
                  (sequence [
             call Oclear_zin [];
             olet (varpat csize)
                  (call Ocout [var cvec; int_const 0])
                  (sequence
                     [if_then (oand (lte (float_const 0.0) (var t))
                                    (lt  (var t) (var horizon)))
                        (ignore (call Odzero []));
                      tuple [var output; var horizon]])])]) };
       { m_name = Oderivatives;
         m_param = [varpat cvec; varpat dvec; varpat t];
         m_body = 
           olet wildpat (call Ocin [var cvec; int_const 0])
                (olet wildpat (call Ostep [var t; void])
                      (sequence [call Odout [var dvec; int_const 0]])) };
       { m_name = Ocrossings;
         m_param = [varpat cvec; varpat zout_vec; varpat t];
         m_body = 
           olet wildpat (call Ocin [var cvec; int_const 0])
                (olet wildpat (call Ostep [var t; void])
                      (sequence [call Ozout [var zout_vec; int_const 0]])) };
       { m_name = Oreset;
         m_param = [varpat cvec];
           m_body = sequence [call Oreset [];
                              ignore (call Ocout [var cvec; int_const 0])]};
      { m_name = Omaxsize; 
         m_param = []; m_body = 
          olet (tuplepat [varpat csize; varpat zsize]) (call Omaxsize [])
            (sequence [oassign_state mcsize (var csize); 
                       oassign_state mzsize (var zsize);
                       tuple [var csize; var zsize]]) };
      { m_name = Ocsize;
        m_param = []; m_body = make (Ostate(Oleft_state_name(mcsize))) };
      { m_name = Ozsize;
        m_param = []; m_body = make (Ostate(Oleft_state_name(mzsize))) }] }
        
let implementation_list impl_list = Misc.iter implementation impl_list
