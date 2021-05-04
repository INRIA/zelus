open Muf
open Muf_rename

let is_flat e =
  let rec flat_expr acc e =
    let acc =
      begin match e.expr with
      | Elet _ -> false
      | _ -> acc
      end
    in
    fold_expr_desc (fun acc _ -> acc) flat_expr acc e.expr
  in 
  flat_expr true e

let rec flatten :
  type a. (a pattern * a expression) list -> a expression -> (a pattern * a expression) list * a expression = begin
    fun acc e ->
      let mk_patt_id n = 
        { patt = Pid {name=n} ; pmeta = Obj.magic() }
      in
      let acc, expr =
        begin match e.expr with
        | Econst _ -> acc, e.expr
        | Evar _ -> acc, e.expr
        | Efield (e, x) -> 
          let acc, e = flatten acc e in
          acc, Efield(e, x)
        | Eapp (e1, e2) -> 
          let acc, e1 = flatten acc e1 in
          let acc, e2 = flatten acc e2 in
          acc, Eapp(e1, e2)
        | Eif (ec, et, ef) -> 
          let acc, ec = flatten acc ec in
          let nt = Muf_rename.freshname "_ft" in
          let nf = Muf_rename.freshname "_ff" in
          (* Efun for et and ef *)
          let p_any = { patt = Pany ; pmeta = Obj.magic() } in          
          let et = { e with expr = Efun(p_any, compile_flatten et) } in
          let ef = { e with expr = Efun(p_any, compile_flatten ef) } in
          let acc = (mk_patt_id nf, ef) :: (mk_patt_id nt, et) :: acc in
          (* Replace et and ef by et' and ef' that are resp. applications of et and ef *)
          let e_args = { e with expr = Econst Cany } in
          let et' = { e with expr = Eapp({e with expr = Evar {name=nt}}, e_args) } in
          let ef' = { e with expr = Eapp({e with expr = Evar {name=nf}}, e_args) } in
          acc, Eif(ec, et', ef')
        | Esequence (e1, e2) -> 
          let acc, e1 = flatten acc e1 in
          let acc, e2 = flatten acc e2 in
          acc, Esequence(e1, e2)
        | Ecall_init e -> 
          let acc, e = flatten acc e in
          acc, Ecall_init e
        | Ecall_step (e1, e2) -> 
          let acc, e1 = flatten acc e1 in
          let acc, e2 = flatten acc e2 in
          acc, Ecall_step(e1, e2)
        | Ecall_reset e -> 
          let acc, e = flatten acc e in
          acc, Ecall_reset e
        | Esample (prob, e) -> 
          let acc, e = flatten acc e in
          acc, Esample(prob, e)
        | Eobserve (prob, e1, e2) -> 
          let acc, e1 = flatten acc e1 in
          let acc, e2 = flatten acc e2 in
          acc, Eobserve(prob, e1, e2)
        | Efactor (prob, e) -> 
          let acc, e = flatten acc e in
          acc, Efactor(prob, e)
        | Einfer (e, id) -> 
          let acc, e = flatten acc e in
          acc, Einfer(e, id)
        | Etuple le -> 
          let rec f acc le acc_e = 
            match le with
            | [] -> acc, List.rev acc_e
            | h::t -> 
              let acc, e = flatten acc h in
              f acc t (e::acc_e)
          in
          let acc, le = f acc le [] in
          acc, Etuple le
        | Erecord (l_se, oe) -> 
          let rec f acc le acc_e = 
            match le with
            | [] -> acc, List.rev acc_e
            | (s,h)::t -> 
              let acc, e = flatten acc h in
              f acc t ((s,e)::acc_e)
          in
          let acc, l_se = f acc l_se [] in
          let acc, oe = 
            begin match oe with 
            | Some e -> 
              let acc, e = flatten acc e in
              acc, Some e
            | _ -> acc, oe
            end
          in
          acc, Erecord (l_se, oe)
        | Elet(p, e1, e2) ->
          let acc, e1 = flatten acc e1 in
          let acc = (p, e1)::acc in
          let acc, e2 = flatten acc e2 in 
          acc, e2.expr
        | Efun _ 
        | Ematch _ 
        | Econstr _ -> assert false
        end
      in acc, {e with expr=expr }
    end

and compile_flatten :
  type a. a expression -> a expression = begin
  fun e -> 
    begin match is_flat e with
      | true -> e
      | false ->     
      let decl, e = flatten [] e in
      let f (p, e1) e2 = { e with expr = (Elet(p, e1, e2)) } in
      List.fold_right f (List.rev decl) e
      end
  end

let compile_node :
  type a. (a pattern, a expression) decl_desc -> (a pattern, a expression) decl_desc = begin
    fun d ->
      begin match d with
      | Dnode (f, params, n) -> 
        let n' =
          let compile_method_with_params (p, e) = (p, compile_flatten e) in
          let compile_class n =
            let ei = compile_flatten n.n_init in
            let ps, es = compile_method_with_params n.n_step in 
            {n with n_init = ei ; n_step = (ps, es)}
          in compile_class n
        in Dnode(f, params, n')
      | _ -> d 
    end
  end

let compile_decl :
  type a. a declaration ->  a declaration = begin
    fun d -> 
      let decl =  
      begin match d.decl with
      | Ddecl (p, e) ->  
        let e = compile_flatten e in 
        Ddecl(p, e)
      | Dfun (f, p, e) -> 
        let e = compile_flatten e in 
        Dfun (f, p, e)
      | Dnode (f, p, n) as dn -> compile_node dn
      | Dtype _ | Dopen _ -> d.decl
      end
    in {decl}
  end

let compile_program :
  type a. a program -> a program = begin
    fun p -> 
      (* rename *)
      let p = Muf_rename.compile_program p in
      (* flatten *)
      let p = List.map compile_decl p in
      p
  end
