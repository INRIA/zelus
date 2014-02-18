(* Translation of resets. They are propagated to function applications *)
(* Distribution of reset under match/with constructs *)
(* It introduces a fresh initialization register for every control branch *)
(* After the transformation, the reset does not have to be distributed *)
(* under control structures *)
(* The transformation is applied on normalized expressions *)
(* "reset
      match e with
      | C1 -> ...
      | C2 -> ...
      end
    every r" is translated into 

   "reset
      init i1 = true
      and init i2 = true
    and match e with
        | C1 -> reset ... and i1 = false every last i1
        | C2 -> reset ... and i2 = false every last i2
        end
    every r" which is then translated into:

    "last_i1 = if r then true else true fby i1
     and last_i2 = if r then true else true fby i2
     and match e with
         | C1 -> reset ... last_i1... and i1 = false and i2 = last_i2 every last_i1
         | C2 -> reset ... last_i2... and i2 = false and i1 = last_i1 every last_i2
         end"

    The initialization "e1 -> e2" under a reset is translated into:

   "if r then e1 else e2"

    "reset
       p = present z1 -> e1 | ... | zn -> en else e init e0
     every r" is translated into

    "reset
       p = present z1 -> (reset e1 every last i1) | ...
                 | zn -> (reset e2 every last i2) else e init e0
       and init i1 = true
       and init i2 = true
       and i1 = false every last i1
       and i2 = fale every last i2
     every r"
*)

open Misc
open Location
open Deftypes
open Zelus
open Ident

(** Build basic operations *)
let make desc ty = 
  { e_desc = desc; e_loc = no_location; e_typ = ty }
let pmake desc ty = { p_desc = desc; p_loc = no_location; p_typ = ty }
let boolpat n = pmake (Evarpat(n)) Initial.typ_bool
let efalse = make (Econst(Ebool(false))) Initial.typ_bool
let etrue = make (Econst(Ebool(true))) Initial.typ_bool
let eqinit i = { eq_desc = EQinit(boolpat i, etrue, None); eq_loc = no_location }
let eqfalse i = { eq_desc = EQeq(boolpat i, efalse); eq_loc = no_location }
let boollast i = make (Elast(i)) Initial.typ_bool

(** Translation of equations. From bottom to top. *)
(** [equation res (eq_list, env) eq = eq_list', env'] *)
(** returns an extended set of equations with env extended accordingly *)
(** [res = true] means that [eq_list] is surrounded by a reset *)
let rec equation res (eq_list, env) ({ eq_desc = desc } as eq) =
  match desc with
    | EQeq _ | EQinit _ | EQnext _ -> eq :: eq_list, env
    | EQmatch(total, e, m_h_list) ->
        (* first compile the body *)
        let m_h_list =
          List.map (fun ({ m_body = b } as h) -> { h with m_body = block res b }) 
            m_h_list in
        if res then
          (* introduce [n] initialization registers *)
          (* [init i_1 = true and ... init i_n = true] *)
          (* transform every branch [b_k] into *)
          (* [reset b_k and i_k = false every last i_k] *)
          let i_list =
            List.map (fun _ -> Ident.fresh "init") m_h_list in
          let env =
            List.fold_left 
              (fun acc i -> 
                Env.add i 
		  { t_typ = Initial.typ_bool; 
                    t_sort = Mem discrete_memory } acc)
	      env i_list in
          let eq_list =
            List.fold_left (fun acc i -> (eqinit i) :: acc) eq_list i_list in
          let m_h_list =
            List.map2
              (fun ({ m_body = b } as h) i -> { h with m_body = reset i b }) 
              m_h_list i_list in
          { eq with eq_desc = EQmatch(total, e, m_h_list) } :: eq_list, env
        else { eq with eq_desc = EQmatch(total, e, m_h_list) } :: eq_list, env
    | EQreset(b, e) ->
        { eq with eq_desc = EQreset(block true b, e) } :: eq_list, env
    | EQder _ | EQemit _ | EQautomaton _ | EQpresent _ -> assert false

and equation_list res env eq_list = List.fold_left (equation res) ([], env) eq_list

and local res ({ l_eq = eq_list; l_env = l_env } as l) =
  let eq_list, l_env = equation_list res l_env eq_list in
  { l with l_eq = eq_list; l_env = l_env }

(** add a [reset ... and i = false every last i] arround a block *)
and reset i ({ b_body = eq_list } as b) =
  { b with
    b_body = 
      [{ eq_desc = EQreset({ b with b_vars = []; b_locals = []; 
	                     b_body = (eqfalse i) :: eq_list; b_env = Env.empty }, 
			   boollast i);
         eq_loc = no_location }] }
  
(** translation of blocks *)
and block res ({ b_vars = n_list; b_body = eq_list; b_env = n_env } as b) =
  (* add local declarations [local x1 in ... in local xn in ...] *)
  let add_locals env n_list n_env =
    let add x entry (n_list, n_env) = x :: n_list, Env.add x entry n_env in
    Env.fold add env (n_list, n_env) in
    
  let eq_list, env = equation_list res Env.empty eq_list in
  let n_list, n_env = add_locals env n_list n_env in
  { b with b_vars = n_list; b_body = eq_list; b_env = n_env }
  
(** The main entry function for expressions. They are supposed to be normalized *)
let rec exp ({ e_desc = desc } as e) =
  match desc with
    | Elet(l, e1) -> { e with e_desc = Elet(local false l, exp e1) }
    | _ -> e
        
let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl(_, { f_kind = A }) -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
          { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
