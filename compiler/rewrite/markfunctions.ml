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

(* Mark functions to be inlined. The analysis is based on the *)
(* causality type system and use the causality tags to decide whether *)
(* a function must be inlined or not *)

open Zelus

type info =
  { inputs: Causal.S.t; (* the causality tags of inputs of the function *)
    outputs: Causal.S.t; (* the causality tags of outputs *)
    o_table: Causal.S.t Causal.M.t; (* outputs of a causality tag *)
    io_table: Causal.S.t Causal.M.t; (* the IO relation for all *)
                                     (* accessible causality tags in the body *)
   }
  
(* For that purpose:
 *- 1/ a first pass computes the set of causality tags
 *- that appear in the body of a function; 
 *- 2/ then the IO for all of them;
 *- 3/ if a function call [f arg1...argn] has to be inlined, it 
 *- is rewritten into [inline f arg1...argn].
 *- the decision is made according to the causality type.
 *- (see the [to_inline] function)
 *- Intuition:
 *- let [f: tc0; arg1: tc1;...; argn: tcn] and [f arg1...argn : tc_res]
 *- The function call is not inlined 
 *- if forall ai, bj st ai in Out tcj, bj in tc_res.
 *-      (io(bj) subseteq io(ai) or io(ai) subseteq io(bj)) and not bj <* ai 
 *- <* is the reflexive/transitive closure of <;
 *- io(a) is the input/dependences of a, with i(a) a subset of names 
 *- from vars tc_in_list and o(a) a subset of names from vars tc_out 
 *- otherwise, the function is inlined 
 *- In such a case, the function call is strict, that is, 
 *- all outputs of the function call already depend 
 *- on all of its inputs *)

(* compute the set of causality tags that appear as input/outputs *)
(* of function applications *)
let funexp_info { f_args = p_list; f_body = ({ e_caus = tc } as e) } =
  let rec exp c_set { e_desc = desc; e_caus = tc } =
    match desc with
    | Elocal _ | Eglobal _ | Econst _
    | Econstr0 _ | Elast _ -> c_set
    | Eapp(_, op, arg_list) ->
        let c_set = List.fold_left exp (exp c_set op) arg_list in
        (* compute the set of causality tags *)
        let tc_list = List.map (fun { e_caus = tc } -> tc) (op :: arg_list) in
        List.fold_left Causal.vars (Causal.vars c_set tc) tc_list
    | Eop(_, e_list) | Etuple(e_list)
    | Econstr1(_, e_list) -> List.fold_left exp c_set e_list
    | Erecord_access(e, _) | Etypeconstraint(e, _) -> exp c_set e
    | Erecord(m_e_list) ->
        List.fold_left (fun acc (_, e) -> exp acc e) c_set m_e_list
    | Erecord_with(e_record, m_e_list) ->
       List.fold_left (fun acc (_, e) -> exp acc e)
		      (exp c_set e_record) m_e_list
    | Epresent(p_h_list, e_opt) ->
        let c_set =
          List.fold_left
            (fun acc { p_body = e } -> exp acc e) c_set p_h_list in
        Misc.optional exp c_set e_opt
    | Ematch(_, e, m_h_list) ->
        List.fold_left
          (fun acc { m_body = e } -> exp acc e) (exp c_set e) m_h_list
    | Elet(l, e) -> exp (local c_set l) e
    | Eblock(b, e) ->  exp (block_eq_list c_set b) e
    | Eseq(e1, e2) -> exp (exp c_set e1) e2
    | Eperiod  { p_phase = p1; p_period = p2 }  ->
       let c_set = Misc.optional exp c_set p1 in
       exp c_set p2

  and local c_set { l_eq = eq_list } = List.fold_left equation c_set eq_list
      
  and equation c_set { eq_desc = desc } =
    match desc with
    | EQeq(_, e) | EQpluseq(_, e) | EQinit(_, e) -> exp c_set e
    | EQder(_, e, e_opt, p_h_list) ->
        let c_set = Misc.optional exp (exp c_set e) e_opt in
        List.fold_left (fun acc { p_body = e } -> exp acc e) c_set p_h_list
    | EQnext(n, e, e_opt) ->
        Misc.optional exp (exp c_set e) e_opt
    | EQautomaton(_, s_h_list, se_opt) ->
        let c_set =
          List.fold_left
            (fun acc { s_body = b_eq_list; s_trans = s_trans } ->
               let acc = block_eq_list acc b_eq_list in
               List.fold_left
                 (fun acc
                   { e_cond = scpat; e_block = b_opt; e_next_state = se } ->
                   let c_set = scondpat acc scpat in
                   let c_set = Misc.optional block_eq_list c_set b_opt in
                   state c_set se)
                 acc s_trans)
            c_set s_h_list in
        Misc.optional state c_set se_opt
    | EQpresent(p_h_list, b_opt) ->
        let c_set =
          List.fold_left
            (fun acc { p_cond = scpat; p_body = b_eq_list } ->
               let acc = scondpat acc scpat in
               block_eq_list acc b_eq_list) c_set p_h_list in
        Misc.optional block_eq_list c_set b_opt
    | EQmatch(_, e, m_h_list) ->
        List.fold_left
          (fun acc { m_body = b_eq_list } -> block_eq_list acc b_eq_list)
          (exp c_set e) m_h_list
    | EQreset(res_eq_list, e) ->
        List.fold_left equation (exp c_set e) res_eq_list
    | EQand(eq_list) | EQbefore(eq_list) ->
        List.fold_left equation c_set eq_list
    | EQemit(_, e_opt) -> Misc.optional exp c_set e_opt
    | EQblock(b) -> block_eq_list c_set b
    | EQforall({ for_index = i_list; for_init = init_list;
	         for_body = b_eq_list }) ->
        let index c_set { desc = desc } =
	  match desc with
          | Einput(_, e) -> exp c_set e
          | Eindex(_, e1, e2) -> exp (exp c_set e1) e2
          | Eoutput _ -> c_set in
        let init c_set { desc = desc } =
	  match desc with
          | Einit_last(_, e) -> exp c_set e in
        let c_set = List.fold_left index c_set i_list in
        let c_set = List.fold_left init c_set init_list in
        block_eq_list c_set b_eq_list
        
  and scondpat c_set { desc = desc } =
    match desc with
    | Econdand(sc1, sc2) | Econdor(sc1, sc2) ->
        scondpat (scondpat c_set sc1) sc2
    | Econdexp(e) | Econdpat(e, _) -> exp c_set e
    | Econdon(sc, e) -> scondpat (exp c_set e) sc
			  
  and state c_set { desc = desc } =
    match desc with
    | Estate0 _ -> c_set
    | Estate1(_, e_list) -> List.fold_left exp c_set e_list
                              
  and block_eq_list c_set { b_locals = l_list; b_body = eq_list } =
    let c_set = List.fold_left local c_set l_list in
    List.fold_left equation c_set eq_list in

  (* First: compute the inputs/outputs of the main function *)
  let tc_list = List.map (fun { p_caus = tc } -> tc) p_list in

  (* mark inputs/outputs *)
  List.iter (Causal.mark_and_polarity false) tc_list;
  Causal.mark_and_polarity true tc;
  let c_set =
    Causal.vars (List.fold_left Causal.vars Causal.S.empty tc_list) tc in
  let inputs, outputs = Causal.ins_and_outs c_set in
  (* computes the set of causality tags that appear in [e] *)
  let c_set = exp c_set e in

  (* compute the table of outputs for all the variables *)
  let o_table = Causal.build_o_table c_set Causal.M.empty in

  (* then the table of io for every causality tag *)
  let io_table = Causal.build_io_table inputs o_table c_set Causal.M.empty in
  { inputs = inputs;
    outputs = outputs;
    io_table = io_table;
    o_table = o_table }
  
(* The function which decides whether or not a function call *)
(* [f(arg1,...,argn) must be inlined *)
let to_inline { io_table = io_table; o_table = o_table } tc_arg_list tc_res =
  let _, out_of_inputs =
    List.fold_left
      (Causal.ins_and_outs_of_a_type true) (Causal.S.empty, Causal.S.empty)
      tc_arg_list in
  let _, out_of_result =
    Causal.ins_and_outs_of_a_type true (Causal.S.empty, Causal.S.empty)
      tc_res in
  (* inline if not [\/_{i in out_of_inputs} IO(i) 
                    subset /\_{j in out_of_result} IO(j)] *)
  (*                or exists o in out_of_result, i in out_of_inputs. path o i *)
  (* if [inline = false], add extra dependences so that all output of the *)
  (* result depends on all inputs. *)
  let inline =
    not (Causal.S.for_all
           (fun i ->
            let io_of_i =
	      try Causal.M.find i io_table with Not_found -> Causal.S.empty in
            Causal.S.for_all
              (fun o ->
               try
		 let io_of_o = Causal.M.find o io_table in
                 not (Causal.strict_path o i) &&
                   (Causal.S.subset io_of_i io_of_o)
	       with Not_found -> true)
              out_of_result)
           out_of_inputs) in
   try
    if not inline then
      Causal.S.iter
        (fun i ->
           Causal.S.iter
             (fun o -> if not (Causal.equal i o) then Causal.less_c i o)
             out_of_result)
        out_of_inputs;
    inline
  with
  | Causal.Clash _ -> assert false
 
(* Mark function calls to be inlined *)
let funexp_mark_to_inline info ({ f_body = e } as funexp) =
  (* generic translation for match handlers *)
  let match_handler body ({ m_body = b } as m_h) =
    { m_h with m_body = body b } in
  
  (* generic translation function for present handlers *)
  let present_handler scondpat body ({ p_cond = sc; p_body = b } as p_h) =
    { p_h with p_cond = scondpat sc; p_body = body b } in

  (* expressions *)
  let rec exp ({ e_desc = desc; e_caus = tc } as e) =
    let desc = match desc with
      | Elocal _ | Eglobal _ | Econst _
      | Econstr0 _ | Elast _ | Eperiod _ -> desc
      | Eop(op, e_list) -> Eop(op, List.map exp e_list)
      | Eapp({ app_inline = i } as app, op, arg_list) ->
          (* only fully applied functions can be inlined *)
	  let op = exp op in
          let arg_list = List.map exp arg_list in
          let i =
            if i then true
            else let tc_arg_list =
                   List.map (fun { e_caus = tc } -> tc) (op :: arg_list) in
                 to_inline info tc_arg_list tc in
          Eapp({ app with app_inline = i }, op, arg_list)
      | Etuple(e_list) -> Etuple(List.map exp e_list)
      | Econstr1(c, e_list) -> Econstr1(c, List.map exp e_list)
      | Erecord_access(e_record, m) -> Erecord_access(exp e_record, m)
      | Erecord(m_e_list) ->
	 Erecord(List.map (fun (m, e) -> (m, exp e)) m_e_list)
      | Erecord_with(e_record, m_e_list) ->
	 Erecord_with(exp e_record,
		      List.map (fun (m, e) -> (m, exp e)) m_e_list)
      | Etypeconstraint(e, ty) -> Etypeconstraint(exp e, ty)
      | Epresent(p_h_list, e_opt) ->
	  Epresent(List.map (present_handler scondpat exp) p_h_list,
	           Misc.optional_map exp e_opt)
      | Ematch(total, e, m_h_list) ->
	 Ematch(total, exp e, List.map (match_handler exp) m_h_list)
      | Elet(l, e) -> Elet(local l, exp e)
      | Eblock(b, e) -> Eblock(block_eq_list b, exp e)
      | Eseq(e1, e2) -> Eseq(exp e1, exp e2) in
    { e with e_desc = desc }

  and local ({ l_eq = eq_list } as l) =
  { l with l_eq = List.map equation eq_list }

  and equation ({ eq_desc = desc } as eq) =
    let desc = match desc with
      | EQeq(p, e) -> EQeq(p, exp e)
      | EQpluseq(n, e) -> EQpluseq(n, exp e)
      | EQder(n, e, e_opt, p_h_list) ->
          EQder(n, exp e, Misc.optional_map exp e_opt,
	        List.map (present_handler scondpat exp) p_h_list)
      | EQinit(n, e) -> EQinit(n, exp e)
      | EQnext(n, e, e_opt) ->
          EQnext(n, exp e, Misc.optional_map exp e_opt)
      | EQautomaton(is_weak, s_h_list, se_opt) ->
          EQautomaton(is_weak, List.map state_handler s_h_list,
		      Misc.optional_map state se_opt)
      | EQpresent(p_h_list, b_opt) ->
          EQpresent(List.map (present_handler scondpat block_eq_list) p_h_list,
		    Misc.optional_map block_eq_list b_opt)
      | EQmatch(total, e, m_h_list) ->
          EQmatch(total, exp e,
	          List.map (match_handler block_eq_list) m_h_list)
      | EQreset(res_eq_list, e) ->
          EQreset(List.map equation res_eq_list, exp e)
      | EQand(and_eq_list) ->
          EQand(List.map equation and_eq_list)
      | EQbefore(before_eq_list) ->
          EQbefore(List.map equation before_eq_list)
      | EQemit(n, e_opt) ->
          EQemit(n, Misc.optional_map exp e_opt)
      | EQblock(b) -> EQblock(block_eq_list b)
      | EQforall({ for_index = i_list; for_init = init_list;
		   for_body = b_eq_list } as body) ->
          let index ({ desc = desc } as ind) =
	    let desc = match desc with
                | Einput(x, e) -> Einput(x, exp e)
	        | Eindex(x, e1, e2) ->
                     Eindex(x, exp e1, exp e2)
	        | Eoutput _ -> desc in
            { ind with desc = desc } in
          let init ({ desc = desc } as ini) =
	    let desc = match desc with
	        | Einit_last(x, e) -> Einit_last(x, exp e) in
            { ini with desc = desc } in
          let i_list = List.map index i_list in
          let init_list = List.map init init_list in
          let b_eq_list = block_eq_list b_eq_list in
          EQforall { body with for_index = i_list; for_init = init_list;
			       for_body = b_eq_list } in
    { eq with eq_desc = desc }

  and scondpat ({ desc = desc } as sc) =
    let desc = match desc with
      | Econdand(sc1, sc2) -> Econdand(scondpat sc1, scondpat sc2)
      | Econdor(sc1, sc2) -> Econdor(scondpat sc1, scondpat sc2)
      | Econdexp(e) -> Econdexp(exp e)
      | Econdpat(e, p) -> Econdpat(exp e, p)
      | Econdon(sc, e) -> Econdon(scondpat sc, exp e) in
    { sc with desc = desc }     
    
  and state_handler ({ s_body = b; s_trans = trans } as sh) =
    { sh with s_body = block_eq_list b; s_trans = List.map escape trans }
    
  and state ({ desc = desc } as se) =
    let desc = match desc with
      | Estate0 _ -> desc
      | Estate1(id, e_list) ->
          Estate1(id, List.map exp e_list) in
    { se with desc = desc }
    
  and block_eq_list ({ b_locals = l_list; b_body = eq_list } as b) =
    { b with b_locals = List.map local l_list;
	     b_body = List.map equation eq_list }
    
  and escape ({ e_cond = sc; e_block = b_opt; e_next_state = se } as esc) =
    { esc with e_cond = scondpat sc;
	       e_block = Misc.optional_map block_eq_list b_opt;
	       e_next_state = state se } in

  { funexp with f_body = exp e }
    
let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
  | Efundecl(n, funexp) ->
      let info = funexp_info funexp in
      let funexp = funexp_mark_to_inline info funexp in
      { impl with desc = Efundecl(n, funexp) }

let implementation_list impl_list =
  Misc.iter implementation impl_list
