open Hybrid
open Misc
open Global
open Deftypes

(* TODO: merge with instantaneousfun: choose one or the other with a variable *)

(** deltadelay translation with offsets;
            + uses functions calls to access and update arrays;
    modified version of LCTES 2011 submission **)

let zlsolve id = Lident.Modname { Lident.qual = "Zlsolve"; Lident.id = id }

let get_cs_op = Eop (zlsolve "get_cs")
let set_cs_op = Eop (zlsolve "set_cs")
let get_zc_op = Eop (zlsolve "get_zc")

let make desc = { desc = desc; loc = Location.no_location }

module FunArgs :
  sig
    val new_args : unit -> pattern

    val x        : unit -> exp
    val dx       : unit -> exp
    val upz      : unit -> exp
    val z        : unit -> exp

    val last_upz : unit -> exp
    val last_z   : unit -> exp

    val discrete : unit -> exp

    val args     : unit -> exp
  end
  =
  struct
    let x        = ref (Ident.fresh "x")
    let dx       = ref (Ident.fresh "dx")
    let upz      = ref (Ident.fresh "upz")
    let z        = ref (Ident.fresh "z")
    let last_upz = ref (Ident.fresh "last_upz")
    let last_z   = ref (Ident.fresh "last_z")
    let discrete = ref (Ident.fresh "discrete")

    let new_args () =
      x        := Ident.fresh "x";
      dx       := Ident.fresh "dx";
      upz      := Ident.fresh "upz";
      z        := Ident.fresh "z";
      (*
      last_upz := Ident.fresh "last_upz";
      last_z   := Ident.fresh "last_z";
      *)
      discrete := Ident.fresh "discrete";
      make (Etuplepat
        (List.map (fun i -> make (Evarpat i)) [!x; !dx; !upz; !z; !discrete]))

    let args () =
      make (Etuple
        (List.map (fun i -> make (Elocal i)) [!x; !dx; !upz; !z; !discrete]))

    let x ()        = make (Elocal !x)
    let dx ()       = make (Elocal !dx)
    let upz ()      = make (Elocal !upz)
    let z ()        = make (Elocal !z)
    let last_upz () = make (Elocal !last_upz)
    let last_z ()   = make (Elocal !last_z)
    let discrete () = make (Elocal !discrete)
  end

let make_let eqs e =
  match eqs with
  | [] -> e
  | _  ->
      let local =
        { l_desc = Elocallet eqs;
          l_env  = Ident.Env.empty; (* TODO: add types for equations *)
          l_loc  = Location.no_location; }
      in
      make (Elet (local, e))

let merge_discrete ed ec =
  make (Eapp (Eifthenelse, [FunArgs.discrete (); ed; ec]))

module type SOLVERVARS =
  sig
    val reset    : Ident.t -> unit      (* pass offset name *)
    val size     : unit -> int

    val add      : exp -> exp -> (exp -> desc) * eq
    (* given an expression that evaluates to an output array
       and an expression giving a value:
       - allocate a cell i
       - returns a function that takes the name of an input array and
         returns an expression that yields the value of the ith cell.
       - and an equation that writes the value into that cell of the
         output array
     *)
    
    val reserve  : int -> exp
    (* reserve the given number of elements, and return
       an offset to pass to a node instantiation *)
  end

module type SOLVER_VARS_ARGS =
  sig
    val get_op : op
  end

module SolverVars (SV : SOLVER_VARS_ARGS) : SOLVERVARS =
  struct
    let i = ref 0
    let offset = ref (Ident.fresh "")
      
    let reset offvar =
      (i := 0; offset := offvar)

    let size () = !i

    let add_to_offset i =
      make (Eapp (Eop (Lident.Name "+"),
            [make (Elocal !offset); make (Econst (Eint i))]))

    let reserve size =
      let ie = !i in
      i := !i + size;
      add_to_offset ie

    let get_element ie in_array =
      Eapp (SV.get_op, [in_array; ie])

    let add out_array out_e =
      let set_element ie = make (Eapp (set_cs_op, [out_array; ie; out_e]))
      in
      let set_decl i =
        make (Eeq (make (Etuplepat []), set_element (add_to_offset i)))
      in
      let ie = !i in
      incr i;
      get_element (add_to_offset ie), set_decl ie
  end

module Cstate = SolverVars (struct
    let get_op = get_cs_op
  end)
module Zeroc = SolverVars (struct
    let get_op = get_zc_op
end)

type ctx =
  { eqs      : eq list;
    post_eqs : eq list }
      
let empty = 
  { eqs = []; post_eqs = [] }

let pair  
  { eqs = eq1; post_eqs = peq1 }
  { eqs = eq2; post_eqs = peq2 }
  =
  { eqs = eq1 @ eq2; post_eqs = peq1 @ peq2 }

(** Find the kind of a global identifier *)
let kind f =
  try
    let { info = { value_typ = { typ_body = typ_body } } } = 
      Modules.find_value f
    in
    (match typ_body with
      | Tvalue _ -> Tany | Tsignature(k, _, _, _) -> k)
  with Not_found ->
    failwith (Printf.sprintf "Kind lookup of '%s' failed." (Lident.modname f))

(* TODO: Does not work! We can't ask for the kinds of local variables.
let lkind x = kind (Modules.longname (Ident.name x))
*)
let lkind x = Tany

(** Find the number of cstate and zeroc elements needed for a function *)
let offsets f =
  try
    match Modules.find_value f with
    | { info = { cont_desc = None } } -> raise Not_found
    | { info = { cont_desc = Some { n_cstate = n_cstate; n_zeroc = n_zeroc } } }
        -> (n_cstate, n_zeroc)
  with Not_found ->
      failwith (Printf.sprintf "Cont size lookup of '%s' failed."
                (Lident.modname f))

let record_offsets f (n_cstate, n_zeroc) =
  try
    let { info = info } = Modules.find_value f in
    info.cont_desc <- Some { n_cstate = n_cstate; n_zeroc = n_zeroc }
  with Not_found ->
      failwith (Printf.sprintf "Cont size lookup of '%s' failed."
                (Lident.modname f))

let pat_of_var_list l = make (Etuplepat(List.map (fun n -> make(Evarpat(n))) l))

let wrap_eqs pre_eqs e post_eqs =
  if List.length pre_eqs = 0 && List.length post_eqs = 0 then e
  else
    let result_id = Ident.fresh "result" in
    let result_v = make (Elocal result_id) in
    let result_eq = make (Eeq (make (Evarpat result_id), e)) in

    let letin = make_let post_eqs result_v in
    let letin = make_let [result_eq] letin in
    make_let pre_eqs letin

let calc_zc read_zc upz =
  let compare_zero v rel =
    make (Eapp (Eop (Lident.Name rel), [v; make (Econst (Efloat 0.0))]))
  in
  let new_z = make (Eapp (Eop (Lident.Name "&&"),
                      [compare_zero (make (read_zc (FunArgs.last_upz ()))) "<";
                       compare_zero (make (Elocal upz)) ">="]))
  in
  make (Eapp (Eop (Lident.Name "||"),
        [make (read_zc (FunArgs.last_upz ())); new_z]))

(** Translate an expression *)
let rec expression e =
  match e.desc with
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ -> e, empty

  | Elast x when lkind x = Tcont ->
      { e with desc = Elocal x }, empty
  
  | Elast _ ->
      e, empty
 
  | Eapp (Eup, [e1]) ->
      let e1, ctx = expression e1 in

      let read_zc, write_zc = Zeroc.add (FunArgs.upz ()) e1 in

      { e with desc = read_zc (FunArgs.z ()) },
      { ctx with post_eqs = write_zc :: ctx.post_eqs }

  | Eapp(Eop(lname) as op, e_list) when kind lname = Tcont ->
      let e_list, ctx = expression_list e_list in
      let (cstate_l, zeroc_l) = offsets lname in
      let offsets =
        make (Etuple [Cstate.reserve cstate_l; Zeroc.reserve zeroc_l])
      in
      { e with desc = Eapp(op, offsets :: FunArgs.args () :: e_list) }, ctx

  | Eapp(op, e_list) ->
      let e_list, ctx = expression_list e_list in
      { e with desc = Eapp(op, e_list) }, ctx

  | Etuple(e_list) ->
      let e_list, ctx = expression_list e_list in
      { e with desc = Etuple(e_list) }, ctx

  | Erecord_access(e1, label) ->
      let e1, ctx = expression e1 in
      { e with desc = Erecord_access(e1, label) }, ctx

  | Erecord(l_e_list) ->
      let l_e_list, ctx = record_list l_e_list in
      { e with desc = Erecord(l_e_list) }, ctx

  | Etypeconstraint(e1, ty) ->
      let e1, ctx = expression e1 in
      { e with desc = Etypeconstraint(e1, ty) }, ctx
  
  | Elet({ l_desc = Elocallet eqs } as local, e1) ->
      let { eqs = eqs1; post_eqs = peqs1 } = equation_list eqs in
      let e1, { eqs = eqs2; post_eqs = peqs2 } = expression e1 in
      (* TODO: we lose the rest of local at this point... *)
      let e1 = wrap_eqs (eqs1 @ eqs2) e1 (peqs1 @ peqs2) in
      e1, empty

  | Elet({ l_desc = Elocalvar _ } as local, e1) ->
      let e1, ctx = expression e1 in
      { e with desc = Elet(local, e1) }, ctx

  | Eseq(e1, e2) ->
      let e1, ctx_e1 = expression e1 in
      let e2, ctx_e2 = expression e2 in
      { e with desc = Eseq(e1, e2) }, pair ctx_e1 ctx_e2
  
  | Eperiod _ -> assert false

and record_list l_e_list =
  match l_e_list with
    | [] -> [], empty
    | (label, e) :: l_e_list ->
        let e, ctx = expression e in
        let l_e_list, ctx_l_e = record_list l_e_list in
        (label, e) :: l_e_list, pair ctx ctx_l_e

and expression_list e_list =
  match e_list with
    | [] -> [], empty
    | e :: e_list ->
        let e, ctx_e = expression e in
        let e_list, ctx = expression_list e_list in
        e :: e_list, pair ctx_e ctx

and equation eq =
  match eq.desc with
  | Eeq(p, e) ->
      let e, ctx = expression e in
      { ctx with eqs = { eq with desc = Eeq(p, e) } :: ctx.eqs }

  | Eder(n, e, e0_opt, h) ->
      let e, ctx = expression e in
      let e0_opt, ctx0 =
        match optional_map expression e0_opt with
        | None -> None, empty
        | Some (e0, ctx0) -> Some e0, ctx0
      in
      let h, ctxh = handler h in
      let ctx = pair ctx (pair ctx0 ctxh) in

      let dx = Ident.fresh (Ident.name n) in
      let out_array = merge_discrete (FunArgs.x ()) (FunArgs.dx ())
      in
      let read_x, write_x = Cstate.add out_array (make (Elocal dx)) in

      let eq_x = make (Eeq(make(Evarpat(n)), make (read_x (FunArgs.x ())))) in
      
      let m_dx = merge_discrete (make (Elocal n)) (e) in
      let eq_dx = 
        { eq with desc = Eactivate(make(Evarpat(dx)), h, Some(m_dx), e0_opt) }
      in
      { eqs = eq_x :: eq_dx :: ctx.eqs; post_eqs = write_x :: ctx.post_eqs }

  | Eactivate(p, h, e_opt, e0_opt) ->
      let e, ctx =
        match e_opt with
          | None -> None, empty
          | Some(e) -> let e, ctx = expression e in Some(e), ctx in
      let e0, ctx0 =
        match e0_opt with
          | None -> None, empty
          | Some(e0) -> let e0, ctx0 = expression e0 in Some(e0), ctx0 in
      let h, ctxh = handler h in
      let ctx = pair ctx (pair ctx0 ctxh) in
      let new_eq = { eq with desc = Eactivate(p, h, e, e0) } in
      { ctx with eqs = new_eq :: ctx.eqs }

  | Einit (p, e) ->
      let e, ctx = expression e in
      let new_eq = { eq with desc = Einit(p, e) } in
      { ctx with eqs = new_eq :: ctx.eqs }

  | Ematch (b, mhs) -> assert false (* TODO: implement this part *)

  | Eautomaton _ | Epresent _ | Ereset _ | Eemit _ -> assert false

and equation_list = function
  | [] -> empty
  | eq :: eq_list ->
      let ctx_eq = equation eq in
      let ctx = equation_list eq_list in
      pair ctx_eq ctx

and handler = function
  | [] -> [], empty
  | (e, ez) :: h ->
      (* TODO: we should leave e unchanged as it is necessarily discrete *)
      (* But that means that the 'last modification' must be changed. *)
      let e, ctx_e = expression e in
      let ez, ctx_ez = expression ez in
      let h, ctx_h = handler h in 
      (e, ez) :: h, pair ctx_e (pair ctx_ez ctx_h)

let implementation impl =
  match impl.desc with
    | Efundecl(f, k, p_list, e) ->
      if k = C then
        let coffset = Ident.fresh "coffset"
        and zoffset = Ident.fresh "zoffset"
        in
        let _ = (Cstate.reset coffset; Zeroc.reset zoffset) in
        let array_args = FunArgs.new_args () in
        let e, { eqs = eqs; post_eqs = post_eqs } = expression e in
        let () = record_offsets (Lident.Name f) (Cstate.size (), Zeroc.size ())
        in
        let offsets =
          make (Etuplepat [make (Evarpat coffset); make (Evarpat zoffset)])
        in
        let e = wrap_eqs eqs e post_eqs
        in
        { impl with desc = Efundecl(f, D, offsets :: array_args :: p_list, e) }
      else impl
    | _ -> impl

let implementation_list impl_list = Misc.iter implementation impl_list
 
(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Generate simulation stubs *)

let filter_fun_types ty_args ty_res = ty_args, ty_res

let state_tallies info =
  let { info = { cont_desc = cont_desc } } = info in
  match cont_desc with
  | None -> assert false
  | Some { n_cstate = n_c; n_zeroc = n_z } -> (n_c, n_z)

let print_main ff qualid fname =
  Format.fprintf ff
    "(* simulation (hybrid) file *)
     let main =
       let mem = %s() in
         %s_step mem (0, 0);;\n" fname fname

