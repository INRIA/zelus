open Muf

module SSet = Set.Make(String)
module IdSet = Set.Make(struct
  type t = identifier
  let compare = compare
end)

let rec fv_patt patt =
  begin match patt.patt with
  | Pid x -> IdSet.singleton x
  | Pconstr(_, None) -> IdSet.empty
  | Pconstr(_, Some p) -> fv_patt p
  | Ptuple l ->
      List.fold_left (fun acc p -> IdSet.union (fv_patt p) acc) IdSet.empty l
  | Pany -> IdSet.empty
  | Pconst _ -> IdSet.empty
  | Ptype (p, _) -> fv_patt p
  end

let rec fv_expr expr =
  begin match expr.expr with
  | Econst _ -> IdSet.empty
  | Econstr (_, None) -> IdSet.empty
  | Econstr (_, Some e) -> fv_expr e
  | Evar x -> IdSet.singleton x
  | Etuple l ->
      List.fold_left (fun acc e -> IdSet.union (fv_expr e) acc) IdSet.empty l
  | Erecord (l, oe) ->
      List.fold_left
        (fun acc (_, e) -> IdSet.union (fv_expr e) acc)
        (Option.fold ~none:IdSet.empty ~some:fv_expr oe) l
  | Efield (e, _) -> fv_expr e
  | Eapp (e1, e2) -> IdSet.union (fv_expr e1) (fv_expr e2)
  | Efun (p, e) -> IdSet.diff (fv_expr e) (fv_patt p)
  | Eif (e, e1, e2) ->
      IdSet.union (fv_expr e) (IdSet.union (fv_expr e1) (fv_expr e2))
  | Ematch (e, cases) ->
      List.fold_left
        (fun acc c ->
          IdSet.union acc
            (IdSet.diff (fv_expr c.case_expr) (fv_patt c.case_patt)))
        (fv_expr e) cases
  | Elet (p, e1, e2) ->
      IdSet.union (fv_expr e1) (IdSet.diff (fv_expr e2) (fv_patt p))
  | Ecall_init e -> fv_expr e
  | Ecall_step (e1, e2) -> IdSet.union (fv_expr e1) (fv_expr e2)
  | Ecall_reset e -> fv_expr e
  | Esequence (e1, e2) -> IdSet.union (fv_expr e1) (fv_expr e2)
  | Esample (_, e) -> fv_expr e
  | Eobserve (_, e1, e2) -> IdSet.union (fv_expr e1) (fv_expr e2)
  | Efactor (_, e) -> fv_expr e
  | Einfer (n, f) -> IdSet.union (fv_expr n) (IdSet.singleton f)
  end

let is_value expr =
  let rec is_value b expr =
    match expr.expr with
    | Erecord (_, Some _) | Eapp _ | Eif _  | Elet _ | Esequence _ | Evar _
    | Ecall_init _ | Ecall_step (_, _) | Ecall_reset _
    | Esample _ | Eobserve _ | Efactor (_, _) | Einfer _ ->
        false
    | Econst _ | Econstr (_, _) | Etuple _ | Efield (_, _)
    | Erecord (_, None)  | Ematch (_, _) ->
        b && fold_expr_desc (fun b _ -> b) is_value b expr.expr
    | Efun _ -> true
  in
  is_value true expr

let is_pure expr =
  let rec is_pure b expr =
    match expr.expr with
    | Eapp _ | Esample _ | Eobserve _ | Einfer _
    | Ecall_init _ | Ecall_step (_, _) | Ecall_reset _ | Efactor (_, _) ->
        false
    | Econst _ | Econstr (_, _) | Evar _ | Etuple _ | Erecord (_, _)
    | Efield (_, _) | Eif (_, _, _) | Ematch (_, _) | Elet (_, _, _)
    | Esequence (_, _)  ->
        b && fold_expr_desc (fun b _ -> b) is_pure b expr.expr
    | Efun _ -> true
  in
  is_pure true expr

let occurences x expr =
  let rec occurences n expr =
    match expr.expr with
    | Evar y -> if x = y then n + 1 else n
    | Elet (p, e1, e2) ->
        let n = occurences n e1 in
        if IdSet.mem x (fv_patt p) then n else occurences n e2
    | e -> fold_expr_desc (fun n _ -> n) occurences n e
  in
  occurences 0 expr

let rec called_functions acc e =
  let acc =
    match e.expr with
    | Eapp ({expr = Evar x}, _) -> IdSet.add x acc
    | _ -> acc
  in
  fold_expr_desc (fun acc _ -> acc) called_functions acc e.expr

let rec eq_patt_expr patt expr =
  match patt.patt, expr.expr with
  | Pid x, Evar y -> x = y
  | Pid _, _ -> false
  | Pconst c1, Econst c2 -> c1 = c2
  | Pconst _, _ -> false
  | Pconstr (x, None), Econstr (y, None) -> x = y
  | Pconstr (x, Some p), Econstr (y, Some e) ->
      x = y && eq_patt_expr p e
  | Pconstr _, _ -> false
  | Pany, _ -> false
  | Ptuple pl, Etuple el ->
      List.length pl = List.length el && List.for_all2 eq_patt_expr pl el
  | Ptuple _, _ -> false
  | Ptype (p, _), _ -> eq_patt_expr p expr


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
    { modul = None; name = x^"__"^(string_of_int !cpt) }

let ident n =
  { modul = None; name = Zident.name n }

let lident (n: Lident.t) =
  let n = Modules.currentname n in
  begin match n with
  | Name x -> { modul = None; name = x }
  | Modname x -> { modul = Some (x.qual); name = x.id }
  end

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

let expr_of_idset s =
  etuple (List.map (fun x -> evar x)
            (IdSet.elements s))

let imported_modules : type a t. a program -> SSet.t = begin
  fun p ->
    let rec modules_expr acc e =
      let acc =
        begin match e.expr with
        | Evar {modul=Some "Stdlib"; name=n} -> acc
        | Evar {modul=Some m; name=n} -> SSet.add m acc
        | _ -> acc
        end
      in
      fold_expr_desc (fun acc _ -> acc) modules_expr acc e.expr
    in

    let rec modules_decl acc d =
      begin match d.decl with
      | Ddecl (_, e) -> modules_expr acc e
      | Dfun (_, _, e) -> modules_expr acc e
      | Dnode (_, _, {n_init=e1 ; n_step=(_,e2)}) -> 
        let set1 = modules_expr acc e1 in
        modules_expr set1 e2
      | Dtype _
      | Dopen _ -> acc
      end
    in 
    List.fold_left modules_decl SSet.empty p
  end
let patt_of_idset s =
  ptuple (List.map (fun x -> pvar x)
            (IdSet.elements s))
