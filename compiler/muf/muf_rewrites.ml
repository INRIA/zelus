open Muf
open Muf_utils

let rec subst x expr1 expr2 =
  match expr2.expr with
  | Evar y -> if x = y then expr1 else expr2
  | Elet (p, e1, e2) when SSet.mem x.name (fv_patt p) ->
      { expr2 with expr = Elet(p, subst x expr1 e1, e2) }
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
  | Pany, _ -> false
  | Ptuple pl, Etuple el -> List.for_all2 eq_patt_expr pl el
  | Ptuple _, _ -> false


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
  | Erecord (l2, (Some { expr = Erecord(l1, Some r); _ })) as e ->
      let diff =
        List.for_all (fun (x, _) -> List.for_all (fun (y, _) -> x <> y) l2) l1
      in
      if diff then { expr with expr = Erecord(l1 @ l2, Some r) }
      else { expr with expr = e }
  | e -> { expr with expr = e }
