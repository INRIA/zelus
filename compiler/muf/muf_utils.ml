open Muf

module SSet = Set.Make(String)

let rec fv_patt patt =
  begin match patt.patt with
  | Pid x -> SSet.singleton x.name
  | Ptuple l ->
      List.fold_left (fun acc p -> SSet.union (fv_patt p) acc) SSet.empty l
  | Pany -> SSet.empty
  | Ptype (p, _) -> fv_patt p
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
  | Ecall_init e -> fv_expr e
  | Ecall_step (e1, e2) -> SSet.union (fv_expr e1) (fv_expr e2)
  | Ecall_reset (e1, e2) -> SSet.union (fv_expr e1) (fv_expr e2)
  | Esequence (e1, e2) -> SSet.union (fv_expr e1) (fv_expr e2)
  | Esample (_, e) -> fv_expr e
  | Eobserve (_, e1, e2) -> SSet.union (fv_expr e1) (fv_expr e2)
  | Efactor (_, e) -> fv_expr e
  | Einfer ((p, body), e) ->
      SSet.union (SSet.diff (fv_expr body) (fv_patt p)) (fv_expr e)
  end

let is_value expr =
  let rec is_value b expr =
    match expr.expr with
    | Erecord (_, Some _) | Eapp _ | Eif _  | Elet _ | Esequence _
    | Esample _ | Eobserve _ | Einfer _ -> false
    | e -> b && fold_expr_desc (fun b _ -> b) is_value b e
  in
  is_value true expr

let occurences x expr =
  let rec occurences n expr =
    match expr.expr with
    | Evar y -> if x = y.name then n + 1 else n
    | Elet (p, e1, e2) ->
        let n = occurences n e1 in
        if SSet.mem x (fv_patt p) then n else occurences n e2
    | e -> fold_expr_desc (fun n _ -> n) occurences n e
  in
  occurences 0 expr

let rec called_functions acc e =
  let acc =
    match e.expr with
    | Eapp ({expr = Evar x}, _) -> SSet.add x.name acc
    | _ -> acc
  in
  fold_expr_desc (fun acc _ -> acc) called_functions acc e.expr
