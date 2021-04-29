open Muf

let freshname = 
  let i = ref 0 in 
  fun prefix -> begin
    incr i;
    prefix ^ "_" ^ (string_of_int !i)
  end

let rec remove_all tbl x =
  begin match Hashtbl.find_opt tbl x with 
  | None -> tbl
  | Some _ -> 
    let _ = Hashtbl.remove tbl x in 
    remove_all tbl x
  end

let rec rename_patt : 
  type a. a pattern -> (string, string) Hashtbl.t -> a pattern * (string, string) Hashtbl.t = begin
  fun p tbl -> 
    let patt = 
      begin match p.patt with
      | Pany | Pconst _-> p.patt
      | Pid {name=n} -> 
        begin match Hashtbl.find_opt tbl n with 
        | Some n -> Pid {name=n}
        | None -> 
          let new_name = freshname n in 
          let _ = Hashtbl.add tbl n new_name in 
          Pid {name=new_name}
        end
      | Ptuple l ->
        let f p tbl = 
          let tbl, p = rename_patt tbl p in p, tbl 
        in
        let tbl, l = List.fold_left_map f tbl l in
        Ptuple l
      | Ptype _ -> assert false
      | Pconstr _ -> assert false
      end
    in { p with patt = patt }, tbl 
  end

let rec rename_expr : 
  type a. a expression -> (string, string) Hashtbl.t -> a expression = begin
  fun e tbl -> 
    let get_name n =
      let n = 
        begin match Hashtbl.find_opt tbl n with
        | None -> n (* free variable, etc *)
        | Some n -> n
        end
      in n
    in
    let rec upd_table p tbl =
      begin match p.patt with
      | Pany | Pconst _-> tbl
      | Pid {name=n} -> 
        let tbl = remove_all tbl n in tbl
      | Ptuple l ->
        let tbl = List.fold_right upd_table l tbl in
        tbl
      | Ptype _ -> assert false
      | Pconstr _ -> assert false
      end
    in
    let rec rename e =
      let expr = 
        begin match e.expr with
        | Econst _ -> e.expr
        | Evar {name=n} -> 
          let n = get_name n in
          Evar {name=n}
        | Elet(p, e1, e2) -> 
          let e1 = rename e1 in 
          let tbl = upd_table p tbl in (* Remove the identifiers in p if they exist in tbl. *)
          let e2 = rename_expr e2 tbl in
          Elet(p, e1, e2)
        | Esample (prob, e) -> 
          let prob = get_name prob in 
          let e = rename e in
          Esample(prob, e)
        | Eobserve (prob, e1, e2) -> 
          let prob = get_name prob in 
          let e1 = rename e1 in
          let e2 = rename e2 in
          Eobserve(prob, e1, e2)
        | Efactor (prob, e) -> 
          let prob = get_name prob in 
          let e = rename e in
          Efactor (prob, e)
        | Einfer (e, id) -> (* The identifier `id` is a node name. *)
          let e = rename e in
          Einfer(e, id)
        | Efield (e, x) -> 
          let e = rename e in
          Efield(e, x)
        | Eapp (e1, e2) -> 
          let e1 = rename e1 in
          let e2 = rename e2 in
          Eapp(e1, e2)
        | Eif (ec, et, ef) -> 
          let et = rename et in
          let ef = rename ef in
          let ec = rename ec in
          Eif(ec, et, ef)
        | Esequence (e1, e2) -> 
          let e1 = rename e1 in
          let e2 = rename e2 in
          Esequence(e1, e2)
        | Ecall_init e -> 
          let e = rename e in
          Ecall_init e
        | Ecall_step (e1, e2) -> 
          let e1 = rename e1 in
          let e2 = rename e2 in
          Ecall_step(e1, e2)
        | Ecall_reset e -> 
          let e = rename e in
          Ecall_reset e
        | Etuple l -> 
          let l = List.map rename l in
          Etuple l
        | Erecord (l_se, oe) -> 
          let l_se = List.map (fun (s,e) -> s, rename e) l_se in
          let oe = 
            begin match oe with 
            | Some e -> 
                let e = rename e in
                Some e
            | _ -> oe
            end
          in
          Erecord (l_se, oe)
        | Ematch _ -> assert false
        | Econstr _ -> assert false
        end
      in { e with expr=expr }
    in rename e
  end

let rec compile_expr :
  type a. a expression -> a expression = begin
    fun e ->
      let expr = 
        begin match e.expr with
        | Econst _ -> e.expr
        | Evar _ -> e.expr
        | Elet(p, e1, e2) ->
          let e1 = compile_expr e1 in
          let p, tbl = rename_patt p (Hashtbl.create 100) in
          let e2 = compile_expr (rename_expr e2 tbl) in
          Elet(p, e1, e2)
        | Efield (e, x) -> 
          let e = compile_expr e in
          Efield(e, x)
        | Eapp (e1, e2) -> 
          let e1 = compile_expr e1 in
          let e2 = compile_expr e2 in
          Eapp(e1, e2)
        | Eif (ec, et, ef) -> 
          let et = compile_expr et in
          let ef = compile_expr ef in
          let ec = compile_expr ec in
          Eif(ec, et, ef)
        | Esequence (e1, e2) -> 
          let e1 = compile_expr e1 in
          let e2 = compile_expr e2 in
          Esequence(e1, e2)
        | Ecall_init e -> 
          let e = compile_expr e in
          Ecall_init e
        | Ecall_step (e1, e2) -> 
          let e1 = compile_expr e1 in
          let e2 = compile_expr e2 in
          Ecall_step(e1, e2)
        | Ecall_reset e -> 
          let e = compile_expr e in
          Ecall_reset e
        | Esample (prob, e) -> 
          let e = compile_expr e in
          Esample(prob, e)
        | Eobserve (prob, e1, e2) -> 
          let e1 = compile_expr e1 in
          let e2 = compile_expr e2 in
          Eobserve(prob, e1, e2)
        | Efactor (prob, e) -> 
          let e = compile_expr e in
          Efactor(prob, e)
        | Einfer (e, id) -> 
          let e = compile_expr e in
          Einfer(e, id)
        | Etuple le -> 
          let le = List.map compile_expr le in
          Etuple le
        | Erecord (l_se, oe) -> 
          let l_se = List.map (fun (s,e) -> s, compile_expr e) l_se in
          let oe = 
            begin match oe with 
            | Some e -> 
              let e = compile_expr e in
              Some e
            | _ -> oe
            end
          in
          Erecord (l_se, oe)
        | Ematch _ -> assert false
        | Econstr _ -> assert false
        end
      in { e with expr=expr }
    end


let compile_node :
  type a. (a pattern, a expression) decl_desc -> (a pattern, a expression) decl_desc = begin
    fun d ->
      begin match d with
      | Dnode (f, params, n) -> 
        let n' =
          let compile_method_with_params (p, e) = (p, compile_expr e) in
          let compile_class n =
            let ei = compile_expr n.n_init in
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
        let e = compile_expr e in 
        Ddecl(p, e)
      | Dfun (f, p, e) -> 
        let e = compile_expr e in 
        Dfun (f, p, e)
      | Dnode (f, p, n) as dn -> compile_node dn
      | Dtype _ | Dopen _ -> d.decl
      end
    in {decl}
  end

let compile_program :
  type a. a program -> a program = begin
    fun p ->
      let p = List.map compile_decl p in
      p
  end
