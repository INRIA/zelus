open Obc
open Muf_compiler_libs
open Muf_compiler_libs.Muf_utils
open Muf_compiler_libs.Ast

exception Not_yet_implemented of string

module SSet = Set.Make(String)

let not_yet_implemented msg =
  raise (Not_yet_implemented msg)

let mk_patt p =
  { patt = p; pmeta = (); }

let mk_expr e =
  { expr = e; emeta = (); }

let mk_decl d =
  { decl = d }

let ident_name n = Ident.name n
let ident n = { name = ident_name n }

let fresh =
  let cpt = ref 0 in
  fun x ->
    incr cpt;
    { name = x^"__"^(string_of_int !cpt) }

let lident_name n =
  let b = Buffer.create 16 in
  let ff_b = Format.formatter_of_buffer b in
  Format.fprintf ff_b "%a" Printer.longname n;
  Format.pp_print_flush ff_b ();
  let x = Buffer.contents b in
  if x.[0] = '(' then "(fun (x,y) -> "^x^" x y)"
  else x

let lident n = { name = lident_name n }

let pany = mk_patt Pany

let eunit = mk_expr (Econst Cunit)
let eany = mk_expr (Econst Cany)

let pvar x = mk_patt (Pid x)
let evar x = mk_expr (Evar x)

let etuple_expr l =
  begin match l with
  | [] -> Econst Cunit
  | [e] -> e
  | l -> Etuple (List.map mk_expr l)
  end

let etuple l =
  begin match l with
  | [] -> eunit
  | [e] -> e
  | l -> mk_expr (Etuple l)
  end

let ptuple l =
  begin match l with
  | [] -> pany
  | [p] -> p
  | l -> mk_patt (Ptuple l)
  end

let expr_of_sset s =
  etuple (List.map (fun x -> evar { name = x })
            (SSet.elements s))

let patt_of_sset s =
  ptuple (List.map (fun x -> pvar { name = x })
            (SSet.elements s))

let self = { name = "self" }
let self_patt = pvar self
let self_expr = evar self

let pack vars e =
  if SSet.is_empty vars then e
  else Etuple [ expr_of_sset vars; mk_expr e ]

let unpack vars p =
  if SSet.is_empty vars then p
  else mk_patt (Ptuple [ patt_of_sset vars; p ])

let rec var_of_left_value v =
  begin match v with
  | Oleft_name x -> ident_name x
  | Oleft_record_access (v, _) -> var_of_left_value v
  | Oleft_index (v, _) -> var_of_left_value v
  end

let rec var_of_left_state_value left =
  begin match left with
  | Oself -> self.name
  | Oleft_instance_name(_n) -> self.name
  | Oleft_state_global(ln) -> lident_name ln
  | Oleft_state_name(_n) -> self.name
  | Oleft_state_record_access(left, _n) -> var_of_left_state_value left
  | Oleft_state_index(left, _idx) -> var_of_left_state_value left
  | Oleft_state_primitive_access(left, _a) -> var_of_left_state_value left
  end

let rec fv_updated i =
  begin match i with
  | Olet(_p, _e, i) -> fv_updated i
  | Oletvar(x, _is_mutable, _ty, _e_opt, i) ->
      SSet.remove (ident_name x) (fv_updated i)
  | Omatch(_e, _match_handler_l) -> not_yet_implemented "fv(match)"
  | Ofor(_is_to, _n, _e1, _e2, i3) -> fv_updated i3
  | Owhile(_e1, i2) -> fv_updated i2
  | Oassign(x, _e) -> SSet.singleton (var_of_left_value x)
  | Oassign_state(left, _e) -> SSet.singleton (var_of_left_state_value left)
  | Osequence l ->
      List.fold_left (fun acc i -> SSet.union (fv_updated i) acc) SSet.empty l
  | Oexp(e) -> fv_expr_updated e
  | Oif(_e, i1, None) -> fv_updated i1
  | Oif(_e, i1, Some i2) -> SSet.union (fv_updated i1) (fv_updated i2)
  end

and fv_expr_updated expr =
  begin match expr with
  | Oconst _ -> SSet.empty
  | Oconstr0 _ -> SSet.empty
  | Oconstr1 (_, e_list) ->
      List.fold_left (fun acc e -> SSet.union (fv_expr_updated e) acc)
        SSet.empty e_list
  | Oglobal _ -> SSet.empty
  | Olocal _ -> SSet.empty
  | Ovar(_is_mutable, n) -> SSet.empty
  | Ostate(l) -> SSet.empty
  | Oaccess(e, eidx) ->
      SSet.union (fv_expr_updated e) (fv_expr_updated eidx)
  | Ovec(e, _se) -> fv_expr_updated e
  | Oupdate(_se, _e1, _i, _e2) -> not_yet_implemented "fv_update: update"
  | Oslice(_e, _s1, _s2) -> not_yet_implemented "fv_update: slice"
  | Oconcat(_e1, _s1, _e2, _s2) -> not_yet_implemented "fv_update: concat"
  | Otuple(e_list) ->
      List.fold_left (fun acc e -> SSet.union (fv_expr_updated e) acc)
        SSet.empty e_list
  | Oapp(e, e_list) ->
      List.fold_left (fun acc e -> SSet.union (fv_expr_updated e) acc)
        (fv_expr_updated e) e_list
  | Omethodcall m ->
      SSet.singleton self.name (* XXX TODO XXX *)
  | Orecord(r) ->
      List.fold_left (fun acc (_, e) -> SSet.union (fv_expr_updated e) acc)
        SSet.empty r
  | Orecord_with(e_record, r) ->
      List.fold_left (fun acc (_, e) -> SSet.union (fv_expr_updated e) acc)
        (fv_expr_updated e_record) r
  | Orecord_access(e_record, lname) -> fv_expr_updated e_record
  | Otypeconstraint(e, _ty_e) -> fv_expr_updated e
  | Oifthenelse(e, e1, e2) ->
      SSet.union (fv_expr_updated e)
        (SSet.union (fv_expr_updated e1) (fv_expr_updated e2))
  | Oinst(i) -> fv_updated i
  end


(* Compilation functions *)

let immediate c =
  begin match c with
  | Oint i -> Cint i
  | Oint32 i -> Cint32 (Int32.of_int i)
  | Ofloat f -> Cfloat (string_of_float f)
  | Obool b -> Cbool b
  | Ostring s -> Cstring s
  | Ochar c -> Cchar c
  | Ovoid -> Cunit
  | Oany -> Cany
  end

let rec pattern patt =
  mk_patt (pattern_desc patt)

and pattern_desc pat =
  begin match pat with
  | Owildpat -> Pany
  | Oconstpat(_) -> Pany
  | Oconstr0pat(_) -> Pany
  | Oconstr1pat(_, _x) -> Pany
  | Ovarpat(n, _ty_exp) -> Pid (ident n)
  | Otuplepat(pat_list) -> Ptuple (List.map pattern pat_list)
  | Oaliaspat(_p, _n) -> not_yet_implemented "pat alias"
  | Oorpat(_pat1, _pat2) -> not_yet_implemented "or pat"
  | Otypeconstraintpat(_p, _ty_exp) -> not_yet_implemented "pat contraint"
  | Orecordpat(_n_pat_list) -> not_yet_implemented "record pat"
  end

let rec expression state_vars e =
  mk_expr (expression_desc state_vars e)

and expression_desc state_vars e =
  begin match e with
  | Oconst c -> pack state_vars (Econst (immediate c))
  | Oconstr0(lname) ->
      pack state_vars (Econst (immediate (Ostring (lident_name lname))))
  | Oconstr1(lname, _e_list) ->
      not_yet_implemented ("expression: constr1("^(lident_name lname)^")")
  | Oglobal(ln) -> pack state_vars (Evar (lident ln))
  | Olocal(n) -> pack state_vars (Evar (ident n))
  | Ovar(_is_mutable, n) -> pack state_vars (Evar (ident n))
  | Ostate(l) -> pack state_vars (left_state_value l)
  | Oaccess(_e, _eidx) -> not_yet_implemented "expression: access"
  | Ovec(_e, _se) -> not_yet_implemented "expression: vec"
  | Oupdate(_se, _e1, _i, _e2) -> not_yet_implemented "expression: update"
  | Oslice(_e, _s1, _s2) -> not_yet_implemented "expression: slice"
  | Oconcat(_e1, _s1, _e2, _s2) -> not_yet_implemented "expression: concat"
  | Otuple(e_list) ->
      let x_e_list = List.map (fun e -> (fresh "_x", e)) e_list in
      let out = etuple_expr (List.map (fun (x, _) ->  Evar x) x_e_list) in
      let k = pack state_vars out in
      List.fold_left
        (fun k (x, e) ->
           Elet(unpack state_vars (pvar x),
                expression state_vars e,
                mk_expr k))
        k x_e_list
  | Oapp(e, e_list) ->
      let x_e_list = List.map (fun e -> (fresh "_x", e)) e_list in
      let args = etuple_expr (List.map (fun (x, _) ->  Evar x) x_e_list) in
      let f = fresh "_f" in
      let out = Eapp (evar f, mk_expr args) in
      let k = pack state_vars out in
      List.fold_left
        (fun k (x, e) ->
           Elet(unpack state_vars (pvar x),
                expression state_vars e,
                mk_expr k))
        k ((f, e) :: x_e_list)
  | Omethodcall m -> method_call state_vars m
  | Orecord(r) ->
      let x_x'_e_list =
        List.map (fun (x,e) -> let x = lident_name x in (x, fresh ("_"^x), e)) r
      in
      let r = List.map (fun (x, x', _) ->  x, evar x') x_x'_e_list in
      let k = pack state_vars (Erecord(r, None)) in
      List.fold_left
        (fun k (_, x', e) ->
           Elet(unpack state_vars (pvar x'),
                expression state_vars e,
                mk_expr k))
        k x_x'_e_list
  | Orecord_with(e_record, r) ->
      let x_x'_e_list =
        List.map (fun (x,e) -> let x = lident_name x in (x, fresh x, e)) r
      in
      let r = List.map (fun (x, x', _) ->  x, evar x') x_x'_e_list in
      let k =
        let x = fresh "_r" in
        Elet(unpack state_vars (pvar x),
                expression state_vars e,
                mk_expr (pack state_vars (Erecord(r, Some (evar x)))))
      in
      List.fold_left
        (fun k (_, x', e) ->
           Elet(unpack state_vars (pvar x'),
                expression state_vars e,
                mk_expr k))
        k x_x'_e_list
  | Orecord_access(e_record, lname) ->
      let x = fresh "_r" in
      let out = Efield (evar x, lident_name lname) in
      Elet(unpack state_vars (pvar x),
           expression state_vars e,
           mk_expr (pack state_vars out))
  | Otypeconstraint(e, _ty_e) ->
      expression_desc state_vars e
  | Oifthenelse(e, e1, e2) ->
      let b = fresh "_b" in
      let out =
        Eif (evar b, expression state_vars e1,
             expression state_vars e2)
      in
      Elet(unpack state_vars (pvar b),
           expression state_vars e,
           mk_expr out)
  | Oinst(i) -> (instruction state_vars i).expr
  end

and left_value left =
  begin match left with
  | Oleft_name x -> Evar (ident x)
  | Oleft_record_access (left, x) ->
      Efield(mk_expr (left_value left), lident_name x)
  | Oleft_index (_, _) -> not_yet_implemented "left_index update"
  end

and left_state_value left =
  match left with
  | Oself -> Evar self
  | Oleft_instance_name(n) -> Efield (self_expr, ident_name n)
  | Oleft_state_global(ln) -> Evar (lident ln)
  | Oleft_state_name(n) -> Efield (self_expr, ident_name n)
  | Oleft_state_record_access(left, n) ->
      Efield (mk_expr (left_state_value left), lident_name n)
  | Oleft_state_index(_left, _idx) ->
      not_yet_implemented "left_state_index"
  | Oleft_state_primitive_access(_left, _a) ->
      not_yet_implemented "primitive_access"

and method_call state_vars m =
  begin match m.met_machine with
  | Some (Lident.Name f)
  | Some (Lident.Modname { Lident.id = f })
    when f = "sample" || f = "observe" || f = "factor" ->
      begin match m.met_name with
      | "reset" -> pack state_vars eunit.expr
      | "copy" -> pack state_vars eunit.expr
      | "step" ->
          begin match f, m.met_args with
          | "sample", [ e ] ->
              let prob = fresh "_prob" in
              let d = fresh "_d" in
              Elet(unpack state_vars (ptuple [pvar prob; pvar d]),
                   expression state_vars e,
                   mk_expr (pack state_vars
                              (Esample(etuple [evar prob; evar d]))))
          | "observe", [ e ] ->
              let prob = fresh "_prob" in
              let d = fresh "_d" in
              let o = fresh "_o" in
              Elet(unpack state_vars (ptuple [pvar prob;
                                              ptuple[ pvar d; pvar o]]),
                   expression state_vars e,
                   mk_expr (pack state_vars
                              (Eobserve(evar prob,
                                        etuple [evar d; evar o]))))
          | "factor", [ e ] ->
              let prob = fresh "_prob" in
              let x = fresh "_x" in
              Elet(unpack state_vars (ptuple [pvar prob; pvar x]),
                   expression state_vars e,
                   mk_expr (pack state_vars
                              (Efactor(etuple [evar prob; evar x]))))

          | _ -> assert false
          end
      | _ -> assert false
      end
  | _ -> standard_method_call m
  end

and standard_method_call m =
  let method_name =
    match m.met_machine with
    | Some name -> { name = (lident_name name) ^ "_" ^ m.met_name }
    | None -> { name =  m.met_name }
  in
  let instantce =
    match m.met_instance with
    | None -> self_expr
    | Some (i, []) -> mk_expr (Efield (self_expr, ident_name i))
    | Some (i, _) -> not_yet_implemented "instance array"
  in
  let x_e_list = List.map (fun e -> (fresh "_x", e)) m.met_args in
  let args = etuple (List.map (fun (x, _) ->  evar x) x_e_list) in
  let k = Eapp (evar method_name, mk_expr (Etuple [instantce; args])) in
  let call =
    List.fold_left
      (fun k (x, e) ->
         let state_vars = fv_expr_updated e in
         Elet(unpack state_vars (pvar x),
              expression state_vars e,
              mk_expr k))
      k x_e_list
  in
  match m.met_instance with
  | None -> call
  | Some (i, []) ->
      let state = fresh ("_" ^ self.name ^ "_" ^ (ident_name i)) in
      let res = fresh ("_res_" ^ (ident_name i)) in
      let self_update =
        mk_expr (Erecord ([ident_name i, evar state], Some self_expr))
      in
      Elet (mk_patt (Ptuple [pvar state; pvar res]),
            mk_expr call,
            mk_expr (Etuple [self_update; evar res]))
  | Some (i, _) -> not_yet_implemented "instance array"

and instruction state_vars i =
  inst state_vars (add_return i)

and inst state_vars i =
  let e = inst_desc state_vars i in
  mk_expr e

and inst_desc state_vars i =
  begin match i with
  | Olet(p, e, i) ->
      let p = pattern p in
      assert (SSet.disjoint (fv_patt p) state_vars);
      let state_vars' = fv_expr_updated e in
      Elet (unpack state_vars' p, expression state_vars' e, inst state_vars i)
  | Oletvar(x, _is_mutable, ty, e_opt, i) ->
      let ty = type_expr_of_typ ty in
      let p = pattern (Ovarpat(x, ty)) in
      assert (SSet.disjoint (fv_patt p) state_vars);
      let e = Option.value ~default:(Oconst Oany) e_opt in
      let state_vars' = fv_expr_updated e in
      Elet (unpack state_vars' p, expression state_vars' e, inst state_vars i)
  | Omatch(_e, _match_handler_l) -> not_yet_implemented "match"
  | Ofor(_is_to, _n, _e1, _e2, _i3) -> not_yet_implemented "for"
  | Owhile(_e1, _i2) -> not_yet_implemented "while"
  | Oassign(left, e) ->
      let updated = fv_expr_updated e in
      Elet (unpack updated (pvar { name = var_of_left_value left }),
            left_value_update updated left e,
            mk_expr (pack state_vars eunit.expr))
  | Oassign_state(left, e) ->
      let updated = fv_expr_updated e in
      Elet (unpack updated (pvar { name = var_of_left_state_value left }),
            left_state_value_update updated left e,
            mk_expr (pack state_vars eunit.expr))
  | Osequence l ->
      begin match List.rev l with
      | [] -> eunit.expr
      | i :: rev_l ->
          List.fold_left
            (fun k i ->
               Elet (unpack state_vars pany, inst state_vars i, mk_expr k))
            (inst_desc state_vars i) l
      end
  | Oexp(e) -> expression_desc state_vars e
  | Oif(e, i1, o_i2) ->
      let i2 = Option.value ~default:(Oexp(Oconst Ovoid)) o_i2 in
      let updated_e = fv_expr_updated e in
      let updated_i = SSet.union (fv_updated i1) (fv_updated i2) in
      let if_ =
        let b = fresh "_b" in
        Elet (unpack updated_e (pvar b),
              expression updated_e e,
              mk_expr (Eif (evar b, inst updated_i i1, inst updated_i i2)))
      in
      let res = fresh "_res_if" in
      Elet (unpack updated_i (pvar res), mk_expr if_,
            mk_expr (pack state_vars (evar res).expr))
  end

and type_expr_of_typ =
  let cpt = ref 0 in
  fun _ty ->
    incr cpt;
    Otypevar ("'a"^(string_of_int !cpt))

and left_value_update state_vars left e =
  begin match left with
  | Oleft_name _ -> expression state_vars e
  | Oleft_record_access (left, x) ->
      let tmp = fresh "_tmp" in
      mk_expr (Elet (unpack state_vars (pvar tmp),
                     expression state_vars e,
                     mk_expr (Erecord([lident_name x, evar tmp],
                                      Some (mk_expr (left_value left))))))
  | Oleft_index (_, _) -> not_yet_implemented "left_index update"
  end

and left_state_value_update state_vars left e =
  begin match left with
  | Oself -> expression state_vars e
  | Oleft_instance_name x ->
      let tmp = fresh "_tmp" in
      mk_expr (Elet (unpack state_vars (pvar tmp),
                     expression state_vars e,
                     mk_expr (Erecord([ident_name x, evar tmp],
                                      Some self_expr))))
  | Oleft_state_global _ln -> expression state_vars e
  | Oleft_state_name n ->
      let tmp = fresh "_tmp" in
      mk_expr (Elet (unpack state_vars (pvar tmp),
                     expression state_vars e,
                     mk_expr (Erecord([ident_name n, evar tmp],
                                      Some self_expr))))
  | Oleft_state_record_access(left, n) ->
      let tmp = fresh "_tmp" in
      mk_expr (Elet (unpack state_vars (pvar tmp),
                     expression state_vars e,
                     mk_expr (Erecord([lident_name n, evar tmp],
                                      Some (mk_expr (left_state_value left))))))
  | Oleft_state_index(_left, _idx) ->
      not_yet_implemented "left_state_index update"
  | Oleft_state_primitive_access(_left, _a) ->
      not_yet_implemented "primitive_access update"
  end

and add_return i =
  begin match i with
  | Olet(p, e, i) -> Olet(p, e, add_return i)
  | Oletvar(x, is_mutable, ty, e_opt, i) ->
      Oletvar(x, is_mutable, ty, e_opt, add_return i)
  | Omatch(_e, _match_handler_l) -> not_yet_implemented "add_return: match"
  | Ofor(is_to, n, e1, e2, i3) ->
      Osequence [ Ofor(is_to, n, e1, e2, i3); Oexp (Oconst (Ovoid)) ]
  | Owhile(e1, i2) -> Osequence [ Owhile(e1, i2); Oexp (Oconst (Ovoid)) ]
  | Oassign(left, e) -> Osequence [ Oassign(left, e); Oexp (Oconst (Ovoid)) ]
  | Oassign_state(left, e) ->
      Osequence [ Oassign_state(left, e); Oexp (Oconst (Ovoid)) ]
  | Osequence l ->
      begin match List.rev l with
      | [] -> Osequence []
      | [ i ] -> add_return i
      | i :: rev_l -> Osequence (List.rev (add_return i :: rev_l))
      end
  | Oexp(e) -> Oexp(e)
  | Oif(e, i1, oi2) ->
      (* assumes Oif returns void *)
      Osequence [ Oif(e, i1, oi2); Oexp (Oconst (Ovoid)) ]
  end

let machine_type name memories instances =
  let i, params, entries =
    List.fold_right
      (fun { m_name = n } (i, params, entries) ->
         let m = Misc.int_to_alpha i in
         (i+1, m :: params, (ident_name n, Tvar m) :: entries))
      memories (0, [], [])
  in
  let i, params, entries =
    List.fold_right
      (fun { i_name = n } (i, params, entries) ->
         let m = Misc.int_to_alpha i in
         (i+1, m :: params, (ident_name n, Tvar m) :: entries))
      instances (i, params, entries)
  in
  mk_decl (Dtype ({ name = "_"^name }, params, TKrecord entries))

let machine_init name i_opt memories instances =
  let memory { m_name = n; m_value = e_opt;
	       m_typ = _ty; m_kind = k_opt; m_size = m_size } =
    begin match k_opt with
    | None ->
       (* discrete state variable *)
        if m_size <> [] then not_yet_implemented "array in memory";
        let e = Option.value ~default:(Oconst Oany) e_opt in
        let state_vars = fv_expr_updated e in
        (ident_name n, expression state_vars e)
    | Some _ -> not_yet_implemented "non discrete memory"
    end
  in
  let instance { i_name = n; i_machine = ei;
		 i_kind = _k; i_params = e_list; i_size = ie_size } =
    if ie_size <> [] then not_yet_implemented "array on instances";
    if e_list <> [] then not_yet_implemented "instance with static parameters";
    begin match ei with
    | Oglobal (Lident.Modname { Lident.id = f })
      when f = "sample"  || f = "observe" || f = "factor" ->
        (ident_name n, eunit)
    | Oglobal x ->
        (ident_name n, evar { name = (lident_name x)^"_init" })
    | Olocal x  | Ovar (_, x) ->
        (ident_name n, evar { name = (ident_name x)^"_init" })
    | _ -> not_yet_implemented "instance is not a name"
    end
  in
  let r =
    mk_expr
      (Erecord
         ((List.map memory memories) @ (List.map instance instances), None))
  in
  mk_decl
    (Ddecl (pvar {name = (name^"_init") },
            match i_opt with
            | None -> r
            | Some i ->
                let state_vars = fv_updated i in
                mk_expr (Elet(unpack state_vars pany,
                              instruction state_vars i,
                              r))))

let machine_method name { me_name = me_name; me_params = pat_list;
                   me_body = i; me_typ = _ty } =
  let method_name = { name = name^"_"^me_name } in
  let args =
    mk_patt (Ptuple [ self_patt;
                      mk_patt (Ptuple (List.map pattern pat_list)) ])
  in
  let state_vars = SSet.add self.name (fv_updated i) in
  let body = instruction state_vars i in
  mk_decl (Dfun(method_name, args, body))

let machine name m =
  if m.ma_params <> [] then
    not_yet_implemented ("static parameters ("^name^")");
  let m_type = machine_type name m.ma_memories m.ma_instances in
  let m_init = machine_init name m.ma_initialize m.ma_memories m.ma_instances in
  let m_methods = List.map (machine_method name) m.ma_methods in
  m_type :: m_init :: m_methods


let implementation impl =
  begin match impl with
  | Oletvalue (x, i) ->
      [  mk_decl (Ddecl (pvar {name = x}, instruction (fv_updated i) i)) ]
  | Oletfun (f, args, i) ->
      let args =
        begin match args with
        | [] -> mk_patt Pany
        | [p] -> pattern p
        | _ -> mk_patt (Ptuple (List.map pattern args))
        end
      in
     [ mk_decl (Dfun ({name = f}, args, instruction (fv_updated i) i)) ]
  | Oletmachine (x, m) ->
      machine x m
  | Oopen m ->
      Format.eprintf "not yet implemented: open %s@." m;
      []
  | Otypedecl _ (* of (string * string list * type_decl) list *) ->
      assert false (* XXX TODO XXX *)
  end

let rewrite_decl f d =
  let rec rewrite_decl n f d =
    let d' = map_decl_desc (fun p -> p) f d in
    if d = d' || n < 0 then d
    else rewrite_decl (n - 1) f d'
  in
  rewrite_decl 1000 f d

let simplify d =
  let r_expr expr =
    let expr = Rewrites.simplify_lets expr in
    let expr = Rewrites.constant_propagation expr in
    expr
  in
  { decl = rewrite_decl r_expr d.decl }

let implementation_list l =
  let l = List.map implementation l in
  let l = List.map (List.map simplify) l in
  l
