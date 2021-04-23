open Muf
open Muf_utils

exception Stop

(** [subst_no_capture x expr1 expr2] substitute [x] by [expr1] in [expr2].
    The substitution fails if some free variables in [expr1] are capture
    in [expr2]
 *)

let subst_no_capture =
  let rec subst fv1 x expr1 expr2 =
    match expr2.expr, expr1.expr with
    | Evar y, _ -> if x = y then expr1 else expr2
    | Elet (p, e1, e2), _ when SSet.mem x.name (fv_patt p) ->
        { expr2 with expr = Elet(p, subst fv1 x expr1 e1, e2) }
    | Elet (p, e1, e2), _ when SSet.mem x.name fv1 ->
        raise Stop
    | Elet (p, e1, e2), _ ->
        let desc = map_expr_desc (fun p -> p) (subst fv1 x expr1) expr2.expr in
        { expr2 with expr = desc }
    | Ematch (_, _), _  -> raise Stop (* XXX TODO XXX *)
    | Esample (prob, e), Evar { name = prob' } ->
        let prob = if x.name = prob then prob' else prob in
        { expr2 with expr = Esample(prob, subst fv1 x expr1 e) }
    | Eobserve (prob, e1, e2), Evar { name = prob' } ->
        let prob = if x.name = prob then prob' else prob in
        { expr2 with expr = Eobserve(prob,
                                     subst fv1 x expr1 e1,
                                     subst fv1 x expr1 e2) }
    | Efactor (prob, e), Evar { name = prob' } ->
        let prob = if x.name = prob then prob' else prob in
        { expr2 with expr = Efactor(prob, subst fv1 x expr1 e) }
    | Econst _, _ | Econstr (_, _), _ | Etuple _, _ | Erecord (_, _), _
    | Efield (_, _), _ | Eapp (_, _), _ | Eif (_, _, _) , _
    | Esequence (_, _), _ | Ecall_init _, _ | Ecall_step (_, _), _
    | Ecall_reset _, _ | Esample (_, _), _ | Eobserve (_, _, _), _
    | Efactor (_, _), _ | Einfer (_, _), _ ->
        let desc = map_expr_desc (fun p -> p) (subst fv1 x expr1) expr2.expr in
        { expr2 with expr = desc }
  in
  fun x expr1 expr2 ->
    try Some (subst (fv_expr expr1) x expr1 expr2)
    with Stop -> None

let rec constant_propagation expr =
  match map_expr_desc (fun p -> p) constant_propagation expr.expr with
  | Elet ({ patt = Pid x; _ }, e1, e2) as expr' when is_value e1 ->
      begin match subst_no_capture x e1 e2 with
      | Some e2 -> e2
      | None -> { expr with expr = expr' }
      end
  | Elet (({ patt = Ptuple ({ patt = Pid x; _ }:: pl); _ } as p),
          ({ expr = Etuple (e :: el); _ } as e1), e2) as expr'
    when is_value e ->
      begin match subst_no_capture x e e2 with
      | None -> { expr with expr = expr' }
      | Some e2' ->
          begin match pl, el with
          | [], _ | _, [] -> assert false
          | [p'], [e'] -> { expr with expr = Elet(p', e', e2') }
          | _, _ ->
              { expr with expr = Elet({ p with patt = Ptuple pl },
                                      { e1 with expr = Etuple el },
                                      e2') }
          end
      end
  | Eif ({expr = Econst (Cbool true)}, e1, _) -> e1
  | Eif ({expr = Econst (Cbool false)}, _, e2) -> e2
  | Ematch (e, cases) as m ->
      begin match List.find_opt (fun c -> eq_patt_expr c.case_patt e) cases with
      | None -> { expr with expr = m }
      | Some case -> case.case_expr
      end
  | e -> { expr with expr = e }

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
      | Some (p, e1) ->
          if eq_patt_expr p e2 then e1
          else { expr with expr = Elet(p, e1, e2) }
      end
  | e -> { expr with expr = e }

let rec simplify_ignore expr =
  match map_expr_desc (fun p -> p) simplify_ignore expr.expr with
  | Elet (p, e1, e2) as e ->
      begin match p.patt with
      | Pany when is_pure e1 -> e2
      | Ptuple [ p1; { patt = Pany} ] ->
          begin match static_fst e1 with
          | None -> { expr with expr = e }
          | Some e1 -> { expr with expr = Elet (p1, e1, e2) }
          end
      | _ -> { expr with expr = e }
      end
  | e -> { expr with expr = e }

and static_fst expr =
  match expr.expr with
  | Econst _ -> None
  | Econstr _ -> None
  | Evar _ -> None
  | Etuple [ e1; e2 ] when is_pure e2 -> Some e1
  | Etuple _ -> None
  | Erecord _ -> None
  | Efield _ -> None
  | Eapp _ -> None
  | Eif (e, e1, e2) ->
      begin match static_fst e1, static_fst e2 with
      | Some e1, Some e2 -> Some { expr with expr = Eif (e, e1, e2) }
      | _, _ -> None
      end
  | Ematch (e, cases) ->
      let ocases =
        List.fold_right
          (fun c acc ->
            match acc with
            | None -> None
            | Some acc ->
                Option.map (fun e -> { c with case_expr = e } :: acc)
                  (static_fst c.case_expr))
          cases (Some [])
      in
      Option.map (fun cases -> { expr with expr = Ematch (e, cases) })
        ocases
  | Elet (p, e1, e2) ->
      Option.map (fun e2 -> { expr with expr = Elet (p, e1, e2) })
        (static_fst e2)
  | Esequence (e1, e2) ->
      Option.map (fun e2 -> { expr with expr = Esequence (e1, e2) })
        (static_fst e2)
  | Ecall_init _ -> None
  | Ecall_step _ -> None
  | Ecall_reset _ -> None
  | Esample _ -> None
  | Eobserve _ -> None
  | Efactor _ -> None
  | Einfer _ -> None


let rec single_and_no_use expr =
  match map_expr_desc (fun p -> p) single_and_no_use expr.expr with
  | Elet({ patt = Pid x; _ }, e1, e2) as e ->
      begin match occurences x.name e2 with
      | 0 when is_pure e1 -> e2
      | 1 ->
          begin match subst_no_capture x e1 e2 with
          | None -> { expr with expr = e }
          | Some e2 -> e2
          end
      | _ -> { expr with expr = e }
      end
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
  | Pconstr (c, None) ->
      let eq = evar { name = "(=)" } in
      mk_expr (Eapp (mk_expr (Eapp(eq, x)), mk_expr (Econstr (c, None))))
  | Pconstr (x, Some _) -> assert false (* XXX TODO XXX *)
  | Ptuple _ -> assert false (* XXX TODO XXX *)
  | Ptype (p, _) -> compile_case_cond x p

and compile_case_body x p e =
  match p.patt with
  | Pany -> e
  | Pconst _ -> e
  | Pconstr (_, None) -> e
  | Pconstr (_, Some _) -> assert false (* XXX TODO XXX *)
  | Pid y -> { e with expr = (Elet (pvar y, x, e)) }
  | Ptuple _ -> assert false (* XXX TODO XXX *)
  | Ptype(p, _) -> compile_case_body x p e
