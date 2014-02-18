(* Discretize the source code by removing ODEs. This turns the initial code *)
(* into valid synchronous code *)
(* for each continuous variable x, we add 3 addtitonal variables : last_x, nx, dx *)
(* [der x  = e init x_init] is turned into [dx =  e] and [nx = last_x + h*dx] and [last_x = x_init -> nx]  *)

open Misc
open Ident
open Hybrid
open Global
open Deftypes

(** Renaming. For every variable [x] defined by its instantaneous derivative *)
(* [der x = ...], build a renaming *)
(* { dname = xi; last_name = last_xi; nname = nxi; reset = r }. *)
(* [r] is true if [x] is reset *)
type renaming =
    { dname: Ident.t;
      lastname: Ident.t;
      nname: Ident.t;
      reset: bool }

(** Basic functions for building terms *)
let make desc ty = { e_desc = desc; e_loc = Location.no_location; e_typ = ty }
let czero = make (Econst (Efloat 0.0)) Initial.typ_float
let cunit = make (Econst Evoid) Initial.typ_unit
let ctrue = make (Econst (Ebool true)) Initial.typ_bool
let cfalse = make (Econst (Ebool false)) Initial.typ_bool

let var n ty = make (Elocal(n)) ty
let varpat n ty = 
  { p_desc = Evarpat(n); p_loc = Location.no_location; p_typ = ty }
let wildpat () = 
  { p_desc = Ewildpat; p_loc = Location.no_location; p_typ = no_typ }
let tuplepat l =
  match l with 
    | [] -> wildpat ()
    | [p] -> p 
    | l -> { p_desc  = Etuplepat(l); p_loc = Location.no_location;
             p_typ = Types.product (List.map (fun { p_typ = ty } -> ty) l) }
let tuple l =
  match l with 
    | [] -> cunit
    | [e] -> e 
    | l -> make (Etuple(l)) (Types.product (List.map (fun { e_typ = ty } -> ty) l))  
let eqmake p e = { eq_desc = Eeq(p, e); eq_loc = Location.no_location }
let floatpat n = { p_desc = Evarpat(n); p_loc = Location.no_location; 
    p_typ = Initial.typ_float }
let boolpat n = { p_desc = Evarpat(n); p_loc = Location.no_location; 
    p_typ = Initial.typ_bool }
let unitpat = { p_desc = Econstpat(Evoid); p_loc = Location.no_location; 
    p_typ = Initial.typ_unit }
let boolvar n = make (Elocal(n)) Initial.typ_bool
let floatvar n = make (Elocal(n)) Initial.typ_float
let boolop op l = 
  make (Eapp(Eop(Lident.Modname(Initial.pervasives_name op)), l)) Initial.typ_bool
let floatop op l = 
  make (Eapp(Eop(Lident.Modname(Initial.pervasives_name op)), l)) Initial.typ_float
let pre e = make (Eapp(Eunarypre, [e])) e.e_typ
let is_ty_unit ty =
  match ty with
  | {t_desc = Tconstr(l, [], _)} -> l = Initial.unit_ident
  | _ -> false
let minusgreater e1 e2 = make (Eapp(Eminusgreater, [e1; e2])) e1.e_typ
let expfromconst c = (make (Econst(Efloat(c))) Initial.typ_float)


(** For every variable [x] which is defined by an equation [der x = ...] *)
(** we introduce three fresh names [last_x], [dx] and [nx] *)
(** The environment is changed so that [kind(x) = Mem] **)
let build_renaming n_list env = 
  let build x ({ t_sort = sort; t_typ = ty } as entry) (renaming0, env) =
    match sort with
      | Mem { m_initialized = m_initialized; m_last = mustlast; m_info = Der(r) } ->
          let last_x = Ident.fresh ("last" ^ (Ident.source x)) in
          let dx = Ident.fresh ("d" ^ (Ident.source x)) in
          let nx = Ident.fresh ("n" ^ (Ident.source x)) in
            Env.add x { dname = dx; lastname = last_x; nname = nx; reset = r} renaming0,
	  (Env.add last_x { t_sort = Mem { m_kind = Tdiscrete; m_initialized = m_initialized;
					   m_last = mustlast; m_info = Def }; t_typ = ty }
	      (Env.add x { t_sort = Mem { m_kind = Tdiscrete; m_initialized = m_initialized;
					  m_last = mustlast; m_info = Def }; t_typ = ty }
		  (Env.add dx { t_sort = Mem { m_kind = Tdiscrete; m_initialized = m_initialized;
					       m_last = mustlast; m_info = Def }; t_typ = ty }
		      (Env.add nx { t_sort = Mem { m_kind = Tdiscrete; m_initialized = m_initialized;
						   m_last = mustlast; m_info = Def }; t_typ = ty }
			  env))))
      | _ -> renaming0, Env.add x entry env in
    Env.fold build env (Env.empty, Env.empty)

(** Makes a default [0] value according to [ty] *)
let rec null ty =
  match ty.t_desc with
    | Tproduct(ty_list) -> tuple (List.map null ty_list)
    | Tlink ty -> null ty
    | Tconstr(l, _, _) when l = Initial.float_ident -> czero
    | Tconstr(l, _, _) when l = Initial.unit_ident -> cunit
    | _ -> assert false

let rec floats_to_bools ty =
  match ty.t_desc with
    | Tproduct(ty_list) ->
        {ty with t_desc = Tproduct (List.map floats_to_bools ty_list) }
    | Tlink ty -> floats_to_bools ty
    | Tconstr(l, _, _) when l = Initial.float_ident -> Initial.typ_bool
    | Tconstr(l, _, _) when l = Initial.unit_ident  -> ty
    | _ -> assert false

let size_of typ =
  let rec sizerec n ty =
    match ty.t_desc with
    | Tconstr(l, _, _) when l = Initial.unit_ident  -> n
    | Tconstr(l, _, _) when l = Initial.float_ident -> n + 1
    | Tconstr(l, _, _) when l = Initial.bool_ident -> n + 1
    | Tproduct(ty_list) -> List.fold_left sizerec n ty_list
    | Tlink ty -> sizerec n ty
    | _ -> assert false in
  sizerec 0 typ

let size_of_states info = (* called by simulator.ml, but for hybrid node, hence not here. *)
  0, 0

let concrete_type loc f = (* called by simulator.ml, but for hybrid node, hence not here. *)
  failwith("concrete type called for a hybrid node that may become discrete")

(** Translation of zero-crossings **)
(* Simple intuition : zerocrossing : x <= 0 at t and x > 0 at next(t)  *)
let up e = 
  (boolop ("&") [minusgreater ctrue 
		    (boolop ("<=") [pre(e); czero]); boolop (">") 
		      [e; czero]])

(** Translation of an ODE: *)
(** 1. [der x = e] produces [dx = e] *)
(** 2. [init x = e] produces [last_x = e0 -> lx]. *)
let der renaming (x, e) loc eq_list =
  let { dname = dx; lastname = last_x; reset = r } = Env.find x renaming in
  let eq_list =
    if r then eq_list
    else (* [x = last_x] *)
      { eq_desc = Eeq(floatpat x, floatvar last_x); eq_loc = loc } :: eq_list in
  let eq_list = 
    { eq_desc = Eeq(floatpat dx, e); eq_loc = loc } :: eq_list in
    eq_list

(** Translation of a pattern. Rename all names *)
let rec pattern renaming ({ p_desc = desc } as p) =
  let desc = match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> desc
    | Etuplepat(p_list) -> Etuplepat(List.map (pattern renaming) p_list)
    | Evarpat(n) -> 
        let { lastname = last_x } = Env.find n renaming in Evarpat(last_x) 
    | Erecordpat(label_pat_list) ->
        Erecordpat(List.map 
                      (fun (label, p) -> (label, pattern renaming p)) label_pat_list)
    | Etypeconstraintpat(p, ty) -> Etypeconstraintpat(pattern renaming p, ty)
    | Ealiaspat(p1, n) -> 
        let { lastname = last_n} = Env.find n renaming in 
        Ealiaspat(pattern renaming p1, last_n)
    | Eorpat(p1, p2) ->
        Eorpat(pattern renaming p1, pattern renaming p2) in
  { p with p_desc = desc }

(** Expression from a pattern. Replace x with last_x *)
let rec exp_of_pat renaming { p_desc = desc; p_loc = loc; p_typ = typ } =
  let desc = match desc with
    | Econstpat(i) -> Econst(i)
    | Econstr0pat(n) -> Econstr0(n)
    | Etuplepat(p_list) -> Etuple(List.map (exp_of_pat renaming) p_list)
    | Evarpat(n) -> 
        begin try let { lastname = lastx } = Env.find n renaming in Elocal(lastx) 
          with | Not_found -> assert false end
    | Erecordpat(label_pat_list) ->
        Erecord(List.map 
                   (fun (label, p) -> (label, exp_of_pat renaming p)) label_pat_list)
    | Etypeconstraintpat(p, ty) -> Etypeconstraint(exp_of_pat renaming p, ty)
    | Ewildpat | Ealiaspat _ | Eorpat _ -> assert false in
  { e_desc = desc; e_loc = loc; e_typ = typ }

(* [last p] returns an expression equal to [p] with every variable [x] from [p] *)
(* is replaced by [last x] *)
let rec last { p_desc = desc; p_typ = ty; p_loc = loc } =
  let desc = match desc with
    | Econstpat(c) -> Econst(c)
    | Econstr0pat(c) -> Econstr0(c)
    | Etuplepat(p_list) -> Etuple(List.map last p_list)
    | Evarpat(n) -> Elast(n)
    | Erecordpat(label_pat_list) ->
        Erecord(List.map (fun (label, p) -> (label, last p)) label_pat_list)
    | Etypeconstraintpat(p, ty) -> Etypeconstraint(last p, ty)
    | Ealiaspat _ | Eorpat _ | Ewildpat _ -> assert false in
  { e_desc = desc; e_typ = ty; e_loc = loc }

(** Introduce an equation [last_pat = e0 -> l_pat] *)
let intro_init renaming pat e0 =
  let last_pat = pattern renaming pat in
  let epat = exp_of_pat renaming pat in
  eqmake last_pat (minusgreater e0 (pre epat))

(** Translating an application. Do a special treatment for zero-crossing *)
(** operators. Leave other applications unchanged. *)
let app op e_list e_result =
  match op, e_list with
    | Einitial, [] -> 
        (* true -> false *)
	minusgreater ctrue cfalse
    | Edisc, [e] -> 
        (* if d then true -> pre x <> x else false *)
        (*ifdiscrete (minusgreater ctrue (boolop ("!=") [pre(e); e])) cfalse*)
	minusgreater ctrue (boolop ("!=") [pre(e); e])
    | Eon, [e1;e2] -> 
        (* e1 and e2 *)
        boolop "&" [e1; e2]
    | op, e_list ->
        { e_result with e_desc = Eapp(op, e_list) }


(* This function adds to eq_list the eqs [nx = last_x+ dx*h] for all continuous variables *)
let add_nx_eqs renaming eq_list =
  Env.fold 
    (fun x { dname = dx; nname = nx; lastname = lastx } acc ->
      (eqmake (floatpat nx) (floatop "+." [(floatvar lastx); (floatop "*."  [(floatvar dx); expfromconst (!Misc.h_allsync)])])) :: acc )
    renaming eq_list

(* The RK4 version of the translation. Does not work yet. *)
let add_nx_eqs_rk4 renaming eq_list =
  Env.fold 
    (fun x { dname = dx; nname = nx; lastname = lastx } acc ->
      let k1 = Ident.fresh ("k1_" ^ (Ident.source x)) in
      let k2 = Ident.fresh ("k2_" ^ (Ident.source x)) in
      let k3 = Ident.fresh ("k3_" ^ (Ident.source x)) in
      let k4 = Ident.fresh ("k4_" ^ (Ident.source x)) in
      let ytemp = Ident.fresh ("ytemp_" ^ (Ident.source x)) in
      let new_slope = floatop "/." [(floatop "+." [ (floatvar k1); (floatop "*." [(floatvar k2); expfromconst 2.0]) ; (floatop "*." [(floatvar k3); expfromconst 2.0]); (floatvar k4)]); expfromconst 6.0] in
	(** Equations for k1, k2, k3, K4, according to the Runge-Kutta-4 method **)
      (eqmake (floatpat k1) (floatvar dx)) ::
        (eqmake (floatpat ytemp) (floatop "+." [(floatvar lastx); (pre(floatop "/."
				  [(floatop "*." [(floatvar k1); expfromconst !Misc.h_allsync]); expfromconst 2.0] ))] )) ::
	(eqmake (floatpat k3) (pre(floatop "/." 
				  [(floatop "*." [(floatvar k2); (make (Econst(Efloat(!Misc.h_allsync))) Initial.typ_float)]);
				   expfromconst 2.0
				  ] ))) ::
	(eqmake (floatpat k4) (pre(floatop "*." [(floatvar k3); expfromconst !Misc.h_allsync ]))) ::

    


	(eqmake (floatpat nx) (floatop "+." [(floatvar lastx);
					     (floatop "*."  [new_slope; (make (Econst(Efloat(!Misc.h_allsync))) Initial.typ_float)])])) ::
	acc)


    renaming eq_list


(** Translation of discrete expressions *)
(* the only job is to replace [last x] by [last_x] when [x] appears in [renaming] *)
let rec expression renaming ({ e_desc = desc } as e) =
  match desc with
    | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ -> e
    | Elast(x) ->
        begin try 
            let { lastname = last_x } = Env.find x renaming in 
            { e with e_desc = Elocal(last_x) } 
          with | Not_found -> e 
        end
    | Eapp(op, e_list) ->
        let e_list = List.map (expression renaming) e_list in
        app op e_list e
    | Etuple(e_list) ->
        { e with e_desc = Etuple(List.map (expression renaming) e_list) }
    | Erecord_access(e1, label) ->
        { e with e_desc = Erecord_access(expression renaming e1, label) }
    | Erecord(l_e_list) ->
        let l_e_list = 
          List.map (fun (label, e) -> (label, expression renaming e)) l_e_list in
        { e with e_desc = Erecord(l_e_list) }
    | Etypeconstraint(e1, ty) ->
        { e with e_desc = Etypeconstraint(expression renaming e1, ty) }
    | Elet(l, e1) ->
        (* as l has been normalized, no derivative is present inside *)
        let l = local renaming l in
        let e1 = expression renaming e1 in
        { e with e_desc = Elet(l, e1) }
    | Eseq(e1, e2) ->
        let e1 = expression renaming e1 in
        let e2 = expression renaming e2 in
        { e with e_desc = Eseq(e1, e2) }
    | Eperiod _ -> e

(** Translation of discrete equations and locals. Only the substitution of *)
(** [last x] by [last_x] when it exists has to be done *)
and equation renaming eq =
  match eq.eq_desc with
    | Eeq(p, e) -> { eq with eq_desc = Eeq(p, expression renaming e) }
    | Einit(p, e) -> { eq with eq_desc = Einit(p, expression renaming e) }
    | Ematch(total, e, m_h_list) ->
        let e = expression renaming e in
        let m_h_list = 
          List.map 
            (fun ({ m_block = b } as m_h) -> { m_h with m_block = block renaming b }) 
            m_h_list in
        { eq with eq_desc = Ematch(total, e, m_h_list) }
    | Ereset(b, e) -> 
      { eq with eq_desc = Ereset(block renaming b, expression renaming e) }
    | Eautomaton _ | Epresent _ | Eder _ | Eemit _ | Eactivate _ -> assert false

and local renaming ({ l_eq = eq_list } as l) =
  { l with l_eq = List.map (equation renaming) eq_list }

and block renaming ({ b_locals = l_list; b_eq = eq_list } as b) =
  { b with b_locals = List.map (local renaming) l_list; 
    b_eq = List.map (equation renaming) eq_list }

(** Translation of continuous computations *)
(* [equation renaming eq_list eq = eq_list'] translates an equation. *)
(* [renaming] is a renamming environment: [x -> dx + lx + last_x + nx] such that every *)
(* occurence of [der x] is replaced by [dx], [last x] by [last_x].
 [nx = dx] is added at the definition point of [x] *)
(* [eq_list] is the already translated sequence of equations to which *)
(* the result is added *)
let rec equation renaming eq_list_current eq =
  match eq.eq_desc with
    | Eeq(p, { e_desc = Eapp(Eup, [e1]) }) ->
        let e1 = expression renaming e1 in
        let e1 = up e1 in
        let eq_e1 = { eq with eq_desc = Eeq(p, e1) } in
        eq_e1 :: eq_list_current
(*    | Eeq(p, ({ e_desc = Eapp(Eop(f), e_list) } as e))  *)
(* app(f) : no need to translate, because no longer additional outputs/inputs*)
(* is it true ? *)
    | Eeq(p, e) ->
        let e = expression renaming e in
        { eq with eq_desc = Eeq(p, e) } :: eq_list_current
    | Eder(x, e, None, []) ->
        (* generate an equation: [dx = e] *)
        let e = expression renaming e in
        der renaming (x, e) eq.eq_loc eq_list_current
    | Einit(pat, e) ->
        (* this is a shortcut for [last_pat = e -> l_pat]) *)
        let e = expression renaming e in
        let eq = try intro_init renaming pat e with Not_found -> eq in
        eq :: eq_list_current
    | Ematch(total, e, m_h_list) ->
        let e = expression renaming e in
        (* project to a list of blocks *)
	let b_list = List.map (fun { m_block = b } -> b) m_h_list in
        let b_list = exclusive_blocks renaming b_list in
        (* then rebuild the list handlers *)
        let m_h_list =
          List.map2 (fun m_h b -> { m_h with m_block = b }) m_h_list b_list in
        let new_eq = { eq with eq_desc = Ematch(total, e, m_h_list) } in
        new_eq :: eq_list_current
    | Ereset(b, e) ->
        let e = expression renaming e in
        let b = block renaming b in
        let new_eq = { eq with eq_desc = Ereset(b, e) } in
        new_eq :: eq_list_current
    | Eemit _ | Epresent _ | Eautomaton _ | Eactivate _ | Eder _ -> assert false

and equation_list renaming eq_list = 
  List.fold_left (equation renaming) [] eq_list

(* translate a list of exclusive blocks. no sharing is done for the moment *)
and exclusive_blocks renaming b_list =
  (* first translate each block in the list *)
  let b_list = List.map (block renaming) b_list in
  b_list

and block renaming ({b_vars = n_list; b_eq = eq_list; b_env = n_env} as b) =
  let renaming0, n_env = build_renaming n_list n_env in
  let renaming = Env.append renaming0 renaming in
  let eq_list = equation_list renaming eq_list in
  let eq_list = add_nx_eqs renaming0 eq_list in
  { b with b_vars = n_list; b_eq = eq_list; b_env = n_env }

and local renaming ({ l_eq = eq_list; l_env = l_env } as l) = 
  let renaming0, l_env = build_renaming [] l_env in
  (* [variables from [eq_list] are modified locally *)
  let renaming_eq_list = Env.append renaming0 renaming in
  let eq_list = equation_list renaming_eq_list eq_list in
  let eq_list = add_nx_eqs renaming0 eq_list in
  renaming, { l with l_eq = eq_list; l_env = l_env }  

let translate_loc renaming ({ l_eq = eq_list; l_env = l_env } as loc) = 
  let renaming0,l_env = build_renaming [] l_env in
  let renaming_eq_list = Env.append renaming0 renaming in
  let eq_list = equation_list renaming_eq_list eq_list in
  let eq_list = add_nx_eqs renaming0 eq_list in
    {loc with l_eq = eq_list; l_env = l_env}

(** Translation of a normalized expression. *)
let rec nexpression e = 
  match e.e_desc with
    | Elet(loc, e1) ->
        let loc = translate_loc Env.empty loc in
        { e with e_desc = Elet(loc, e1) }
    | _ -> e

let set_cont_desc f =
  Global.set_cont_desc (Modules.find_value (Lident.Name(f))) None

let implementation impl =
  match impl.desc with
    | Efundecl(f, ({ f_kind = C; f_args = p_list; f_body = e } as body)) ->
        (* Translation of f body *)
        let e = nexpression e in
        set_cont_desc f; (* Cont_Desc set to none. Is it useful ? *)
	Global.set_discrete (Modules.find_value (Lident.Name(f)));  (* Change the function type from continuous to discrete *)
        (* final output *)
        { impl with desc =
            Efundecl(f, { body with f_kind = D; f_args = p_list; f_body = e }) }
    | _ -> impl

let implementation_list impl_list = Misc.iter implementation impl_list

