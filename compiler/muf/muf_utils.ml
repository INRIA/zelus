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
  | Efun (p, e) -> SSet.diff (fv_expr e) (fv_patt p)
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
    | Econst _ | Econstr (_, _) | Evar _ | Etuple _ | Efield (_, _)
    | Erecord (_, None)  | Ematch (_, _)
    | Ecall_init _ | Ecall_step (_, _) | Ecall_reset _ | Efactor (_, _) ->
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

let rec eq_patt_expr patt expr =
  match patt.patt, expr.expr with
  | Pid x, Evar y -> x = y
  | Pid _, _ -> false
  | Pconst c1, Econst c2 -> c1 = c2
  | Pconst _, _ -> false
  | Pconstr (x, None), Econstr (y, None) -> x.name = y.name
  | Pconstr (x, Some p), Econstr (y, Some e) ->
      x.name = y.name && eq_patt_expr p e
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

let imported_modules : type a t. a program -> SSet.t = begin
  fun p ->
    let rec modules_expr acc e =
      let acc =
        begin match e.expr with
        | Evar {name=n} ->
          let first_is_upper = 
            let first = n.[0] in
            first = Char.uppercase_ascii first      
          in 
          if first_is_upper then
            begin match String.index_opt n '.' with
            | None -> acc
            | Some idx -> SSet.add (String.sub n 0 idx) acc
            end
          else
            acc
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