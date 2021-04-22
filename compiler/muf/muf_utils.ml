open Muf

module SSet = Set.Make(String)

let rec fv_patt patt =
  begin match patt.patt with
  | Pid x -> SSet.singleton x.name
  | Pconstr(_, None) -> SSet.empty
  | Pconstr(_, Some p) -> fv_patt p
  | Ptuple l ->
      List.fold_left (fun acc p -> SSet.union (fv_patt p) acc) SSet.empty l
  | Pany -> SSet.empty
  | Pconst _ -> SSet.empty
  | Ptype (p, _) -> fv_patt p
  end

let rec fv_expr expr =
  begin match expr.expr with
  | Econst _ -> SSet.empty
  | Econstr (_, None) -> SSet.empty
  | Econstr (_, Some e) -> fv_expr e
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
  | Ematch (e, cases) ->
      List.fold_left
        (fun acc c ->
          SSet.union acc
            (SSet.diff (fv_expr c.case_expr) (fv_patt c.case_patt)))
        (fv_expr e) cases
  | Elet (p, e1, e2) ->
      SSet.union (fv_expr e1) (SSet.diff (fv_expr e2) (fv_patt p))
  | Ecall_init e -> fv_expr e
  | Ecall_step (e1, e2) -> SSet.union (fv_expr e1) (fv_expr e2)
  | Ecall_reset e -> fv_expr e
  | Esequence (e1, e2) -> SSet.union (fv_expr e1) (fv_expr e2)
  | Esample (_, e) -> fv_expr e
  | Eobserve (_, e1, e2) -> SSet.union (fv_expr e1) (fv_expr e2)
  | Efactor (_, e) -> fv_expr e
  | Einfer (n, f) -> SSet.union (fv_expr n) (SSet.singleton f.name)
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

(** Expression Builders *)

let mk_patt p =
  { patt = p; pmeta = (); }

let mk_expr e =
  { expr = e; emeta = (); }

let mk_decl d =
  { decl = d }

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
  x

let lident n = { name = lident_name n }

let pany = mk_patt Pany

let eunit = mk_expr (Econst Cunit)
let eany = mk_expr (Econst Cany)

let pvar x = mk_patt (Pid x)
let evar x = mk_expr (Evar x)

let einfer_init n f = mk_expr (Einfer (n, f))

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
