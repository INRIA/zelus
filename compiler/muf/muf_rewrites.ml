open Muf
open Muf_utils

let rec subst x expr1 expr2 =
  match expr2.expr, expr1.expr with
  | Evar y, _ -> if x = y then expr1 else expr2
  | Elet (p, e1, e2), _ when SSet.mem x.name (fv_patt p) ->
      { expr2 with expr = Elet(p, subst x expr1 e1, e2) }
  | Esample (prob, e), Evar { name = prob' } ->
      let prob = if x.name = prob then prob' else prob in
      let desc = map_expr_desc (fun p -> p) (subst x expr1) e.expr in
      { expr2 with expr = Esample(prob, { e with expr = desc }) }
  | Eobserve (prob, e1, e2), Evar { name = prob' } ->
      let prob = if x.name = prob then prob' else prob in
      let desc1 = map_expr_desc (fun p -> p) (subst x expr1) e1.expr in
      let desc2 = map_expr_desc (fun p -> p) (subst x expr1) e2.expr in
      { expr2 with expr = Eobserve(prob,
                                   { e1 with expr = desc1 },
                                   { e2 with expr = desc2 }) }
  | Efactor (prob, e), Evar { name = prob' } ->
      let prob = if x.name = prob then prob' else prob in
      let desc = map_expr_desc (fun p -> p) (subst x expr1) e.expr in
      { expr2 with expr = Efactor(prob, { e with expr = desc }) }
  | _ ->
      let desc = map_expr_desc (fun p -> p) (subst x expr1) expr2.expr in
      { expr2 with expr = desc }

let rec constant_propagation expr =
  match map_expr_desc (fun p -> p) constant_propagation expr.expr with
  | Elet ({ patt = Pid x; _ }, e1, e2) when is_value e1 -> subst x e1 e2
  | Elet (({ patt = Ptuple ({ patt = Pid x; _ }:: pl); _ } as p),
          ({ expr = Etuple (e :: el); _ } as e1), e2)
    when is_value e ->
      begin match pl, el with
      | [], _ | _, [] -> assert false
      | [p'], [e'] -> { expr with expr = Elet(p', e', subst x e e2) }
      | _, _ -> { expr with expr = Elet({ p with patt = Ptuple pl },
                                        { e1 with expr = Etuple el },
                                        subst x e e2) }
      end
  | e -> { expr with expr = e }


let rec eq_patt_expr patt expr =
  match patt.patt, expr.expr with
  | Pid x, Evar y -> x = y
  | Pid _, _ -> false
  | Pconst c1, Econst c2 -> c1 = c2
  | Pconst _, _ -> false
  | Pany, _ -> false
  | Ptuple pl, Etuple el -> List.for_all2 eq_patt_expr pl el
  | Ptuple _, _ -> false
  | Ptype (p, _), _ -> eq_patt_expr p expr

let rec simplify_let patt expr =
  match patt.patt, expr.expr with
  | Pany, _ when is_value expr -> None
  | Ptuple pl, Etuple el ->
      let pel =
        List.fold_right2
          (fun p e acc ->
             match simplify_let p e with
             | None -> acc
             | Some (p, e) -> (p, e)::acc)
          pl el []
      in
      begin match pel with
      | [] -> None
      | [p1, e1] -> Some (p1, e1)
      |  _ ->
          let pl, el = List.split pel in
          Some ({ patt with patt = Ptuple pl }, { expr with expr = Etuple el })
      end
  | _ -> if eq_patt_expr patt expr then None else Some (patt, expr)

let rec simplify_lets expr =
  match map_expr_desc (fun p -> p) simplify_lets expr.expr with
  | Elet(p, e1, e2) ->
      begin match simplify_let p e1 with
      | None -> e2
      | Some (p, e1) -> { expr with expr = Elet(p, e1, e2) }
      end
  | e -> { expr with expr = e }

let rec single_use expr =
  match map_expr_desc (fun p -> p) single_use expr.expr with
  | Elet({ patt = Pid x; _ }, e1, e2) when occurences x.name e2 = 1 ->
      subst x e1 e2
  | e -> { expr with expr = e }

let rec merge_record_update expr =
  match map_expr_desc (fun p -> p) merge_record_update expr.expr with
  | Erecord (l2, (Some { expr = Erecord(l1, r); _ })) ->
      let diff = (* l1 - l2 *)
        List.filter (fun (x, _) -> not (List.mem_assoc x l2)) l1
      in
      { expr with expr = Erecord(diff @ l2, r) }
  | e -> { expr with expr = e }

let rec simplify_record_access expr =
  match map_expr_desc (fun p -> p) simplify_record_access expr.expr with
  | Efield ({ expr = Erecord(l, _) }, x) ->
      begin match List.assoc_opt x l with
      | Some e -> e
      | None -> expr
      end
  | e -> { expr with expr = e }


let rec remove_match expr =
  match map_expr_desc (fun p -> p) remove_match expr.expr with
  | Ematch (e, cases) ->
      let x = fresh "x" in
      { expr with expr = Elet(pvar x, e, compile_cases (evar x) cases) }
  | e -> { expr with expr = e }

and compile_cases x cases =
  match cases with
  | [ ] -> assert false
  | [ { case_expr = e } ] -> e
  | { case_patt = p; case_expr = e } :: cases ->
      { e with expr = Eif (compile_case_cond x p,
                           compile_case_body x p e,
                           compile_cases x cases) }

and compile_case_cond x p =
  match p.patt with
  | Pid _ | Pany -> mk_expr (Econst (Cbool true))
  | Pconst c ->
      let eq = evar { name = "(=)" } in
      mk_expr (Eapp (mk_expr (Eapp(eq, x)), mk_expr (Econst c)))
  | Ptuple _ -> assert false (* XXX TODO XXX *)
  | Ptype (p, _) -> compile_case_cond x p

and compile_case_body x p e =
  match p.patt with
  | Pany -> e
  | Pconst _ -> e
  | Pid y -> { e with expr = (Elet (pvar y, x, e)) }
  | Ptuple _ -> assert false (* XXX TODO XXX *)
  | Ptype(p, _) -> compile_case_body x p e
