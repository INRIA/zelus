open Obc
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

let lident_name n =
  let b = Buffer.create 16 in
  let ff_b = Format.formatter_of_buffer b in
  Format.fprintf ff_b "%a" Printer.longname n;
  Format.pp_print_flush ff_b ();
  Buffer.contents b

let lident n = { name = lident_name n }

let eunit = mk_expr (Econst Cunit)
let eany = mk_expr (Econst Cany)

let self = { name = "self" }
let self_patt = mk_patt (Pid { name = "self" })
let self_expr = mk_expr (Evar { name = "self" })

let rec fv_patt patt =
  begin match patt.patt with
  | Pid x -> SSet.singleton x.name
  | Ptuple l ->
      List.fold_left (fun acc p -> SSet.union (fv_patt p) acc) SSet.empty l
  | Pany -> SSet.empty
  end

let rec fv_expr expr =
  begin match expr.expr with
  | Econst _ -> SSet.empty
  | Evar x -> SSet.singleton x.name
  | Etuple l ->
      List.fold_left (fun acc e -> SSet.union (fv_expr e) acc) SSet.empty l
  | Erecord (l, oe) ->
      List.fold_left
        (fun acc (_, e) -> SSet.union (fv_expr e) acc)
        (Option.fold ~none:SSet.empty ~some:fv_expr oe) l
  | Efield (e, _) -> fv_expr e
  | Eapp (e1, e2) -> SSet.union (fv_expr e1) (fv_expr e2)
  | Eif (e, e1, e2) ->
      SSet.union (fv_expr e) (SSet.union (fv_expr e1) (fv_expr e2))
  | Elet (p, e1, e2) ->
      SSet.union (fv_expr e1) (SSet.diff (fv_expr e2) (fv_patt p))
  | Esequence (e1, e2) -> SSet.union (fv_expr e1) (fv_expr e2)
  | Esample e -> fv_expr e
  | Eobserve (e1, e2) -> SSet.union (fv_expr e1) (fv_expr e2)
  | Einfer ((p, body), e) ->
      SSet.union (SSet.diff (fv_expr body) (fv_patt p)) (fv_expr e)
  end


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

let rec expression e =
  mk_expr (expression_desc e)

and expression_desc e =
  begin match e with
  | Oconst c -> Econst (immediate c)
  | Oconstr0(lname) -> Econst (immediate (Ostring (lident_name lname)))
  | Oconstr1(lname, _e_list) ->
      not_yet_implemented ("expression: constr1("^(lident_name lname)^")")
  | Oglobal(ln) -> Evar (lident ln)
  | Olocal(n) -> Evar (ident n)
  | Ovar(_is_mutable, n) -> Evar (ident n)
  | Ostate(l) -> left_state_value l
  | Oaccess(_e, _eidx) -> not_yet_implemented "expression: access"
  | Ovec(_e, _se) -> not_yet_implemented "expression: vec"
  | Oupdate(_se, _e1, _i, _e2) -> not_yet_implemented "expression: update"
  | Oslice(_e, _s1, _s2) -> not_yet_implemented "expression: slice"
  | Oconcat(_e1, _s1, _e2, _s2) -> not_yet_implemented "expression: concat"
  | Otuple(e_list) -> Etuple (List.map expression e_list)
  | Oapp(e, e_list) ->
      let args =
        match List.map expression e_list with
        | [] -> eunit
        | [e] -> e
        | args -> mk_expr (Etuple args)
      in
      Eapp (expression e, args)
  | Omethodcall m -> assert false (* method_call m *)
  | Orecord(r) ->
      Erecord (List.map (fun (x, e) -> ((lident_name x), expression e)) r, None)
  | Orecord_with(e_record, r) ->
      Erecord (List.map (fun (x, e) -> ((lident_name x), expression e)) r,
               Some (expression e_record))
  | Orecord_access(e_record, lname) ->
      Efield (expression e_record, lident_name lname)
  | Otypeconstraint(e, _ty_e) ->
      (expression e).expr
  | Oifthenelse(e, e1, e2) ->
      Eif (expression e, expression e1, expression e2)
  | Oinst(i) -> (instruction i).expr
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

and method_call p m k =
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
  let inputs = List.map expression m.met_args in
  let args =
    match inputs with
    | [] -> eunit
    | [e] -> e
    | args -> mk_expr (Etuple args)
  in
  let call =
    mk_expr
      (Eapp (mk_expr (Evar method_name), mk_expr (Etuple [instantce; args])))
  in
  match m.met_instance with
  | None -> Elet (mk_patt (Ptuple [self_patt; p]), call, k)
  | Some (i, []) ->
      let call =
        let state = { name = (self.name ^ "_" ^ (ident_name i)) } in
        let res = { name = ("res_" ^ (ident_name i)) } in
        let self_update =
          mk_expr (Erecord ([ident_name i, mk_expr (Evar state)],
                            Some self_expr))
        in
        Elet (mk_patt (Ptuple [mk_patt (Pid state); mk_patt (Pid res)]),
              call,
              mk_expr (Etuple [self_update; mk_expr (Evar res)]))
      in
      Elet (mk_patt (Ptuple [self_patt; p]), mk_expr call, k)
  | Some (i, _) -> not_yet_implemented "instance array"

and instruction i =
  let k = expr_of_sset (fv_updated i) in
  inst i k

and inst i k =
  let e = inst_desc i k in
  mk_expr e

and inst_desc i k =
  begin match i with
  | Olet(p, Omethodcall m, i) ->
      let p = pattern p in
      assert (SSet.disjoint (fv_patt p) (fv_expr k));
      method_call p m (inst i k)
  | Olet(p, e, i) ->
      let p = pattern p in
      assert (SSet.disjoint (fv_patt p) (fv_expr k));
      Elet (p, expression e, inst i k)
  | Oletvar(x, _is_mutable, ty, e_opt, i) ->
      let ty = type_expr_of_typ ty in
      let p = pattern (Ovarpat(x, ty)) in
      assert (SSet.disjoint (fv_patt p) (fv_expr k));
      let e = Option.value ~default:(Oconst Oany) e_opt in
      Elet (p, expression e, inst i k)
  | Omatch(_e, _match_handler_l) -> not_yet_implemented "match"
  | Ofor(_is_to, _n, _e1, _e2, _i3) -> not_yet_implemented "for"
  | Owhile(_e1, _i2) -> not_yet_implemented "while"
  | Oassign(left, e) ->
      Elet (mk_patt (Pid { name = var_of_left_value left }),
            left_value_update left e,
            k)
  | Oassign_state(left, e) ->
      Elet (mk_patt (Pid { name = var_of_left_state_value left }),
            left_state_value_update left e,
            k)
  | Osequence l -> (List.fold_right inst l k).expr
  | Oexp(Omethodcall m) ->
      let k = mk_expr (Etuple [k; eunit]) in
      method_call (mk_patt Pany) m k
  | Oexp(e) -> Etuple [k; expression e]
  | Oif(e, i1, None) ->
      let updated = fv_updated i1 in
      let p = patt_of_sset updated in
      let k' = expr_of_sset updated in
      let if_ = mk_expr (Eif (expression e, inst i1 k', k')) in
      Elet (p,  if_, k)
  | Oif(e, i1, Some i2) ->
      let updated = SSet.union (fv_updated i1) (fv_updated i2) in
      let p = patt_of_sset updated in
      let k' = expr_of_sset updated in
      let if_ = mk_expr (Eif (expression e, inst i1 k', inst i2 k')) in
      Elet (p,  if_, k)
  end

and type_expr_of_typ =
  let cpt = ref 0 in
  fun _ty ->
    incr cpt;
    Otypevar ("'a"^(string_of_int !cpt))

and expr_of_sset s =
  begin match SSet.elements s with
  | [] -> eunit
  | [x] -> mk_expr (Evar { name = x })
  | l -> mk_expr (Etuple (List.map (fun x -> mk_expr (Evar { name = x })) l))
  end

and patt_of_sset s =
  begin match SSet.elements s with
  | [] -> mk_patt Pany
  | [x] -> mk_patt (Pid { name = x })
  | l -> mk_patt (Ptuple (List.map (fun x -> mk_patt (Pid { name = x })) l))
  end

and left_value_update left e =
  begin match left with
  | Oleft_name _ -> expression e
  | Oleft_record_access (left, x) ->
      mk_expr (Erecord([lident_name x, expression e],
                       Some (mk_expr (left_value left))))
  | Oleft_index (_, _) -> not_yet_implemented "left_index update"
  end

and left_state_value_update left e =
  begin match left with
  | Oself -> expression e
  | Oleft_instance_name x ->
      mk_expr (Erecord([ident_name x, expression e], Some self_expr))
  | Oleft_state_global _ln -> expression e
  | Oleft_state_name n ->
      mk_expr (Erecord([ident_name n, expression e], Some self_expr))
  | Oleft_state_record_access(left, n) ->
      mk_expr (Erecord([lident_name n, expression e],
                       Some (mk_expr (left_state_value left))))
  | Oleft_state_index(_left, _idx) ->
      not_yet_implemented "left_state_index update"
  | Oleft_state_primitive_access(_left, _a) ->
      not_yet_implemented "primitive_access update"

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
        (ident_name n, Option.fold ~none:eany ~some:expression e_opt)
    | Some _ -> not_yet_implemented "non discrete memory"
    end
  in
  let instance { i_name = n; i_machine = ei;
		 i_kind = _k; i_params = e_list; i_size = ie_size } =
    if ie_size <> [] then not_yet_implemented "array on instances";
    if e_list <> [] then not_yet_implemented "instance with static parameters";
    begin match ei with
    | Oglobal x ->
        (ident_name n, mk_expr (Evar { name = (lident_name x)^"_init" }))
    | Olocal x  | Ovar (_, x) ->
        (ident_name n, mk_expr (Evar { name = (ident_name x)^"_init" }))
    | _ -> not_yet_implemented "instance is not a name"
    end
  in
  let r =
    mk_expr
      (Erecord
         ((List.map memory memories) @ (List.map instance instances), None))
  in
  mk_decl
    (Ddecl (mk_patt (Pid {name = (name^"_init") }),
            match i_opt with
            | None -> r
            | Some i -> mk_expr (Esequence (instruction i, r))))

let machine_method name { me_name = me_name; me_params = pat_list;
                   me_body = i; me_typ = _ty } =
  let method_name = { name = name^"_"^me_name } in
  let args =
    mk_patt (Ptuple [ self_patt;
                      mk_patt (Ptuple (List.map pattern pat_list)) ])
  in
  let body = instruction i in
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
      [  mk_decl (Ddecl (mk_patt (Pid {name = x}), instruction i)) ]
  | Oletfun (f, args, i) ->
      let args =
        begin match args with
        | [] -> mk_patt Pany
        | [p] -> pattern p
        | _ -> mk_patt (Ptuple (List.map pattern args))
        end
      in
     [ mk_decl (Dfun ({name = f}, args, instruction i)) ]
  | Oletmachine (x, m) ->
      machine x m
  | Oopen _m -> not_yet_implemented "open"
  | Otypedecl _ (* of (string * string list * type_decl) list *) ->
      assert false (* XXX TODO XXX *)
  end


let implementation_list l =
  List.map implementation l
