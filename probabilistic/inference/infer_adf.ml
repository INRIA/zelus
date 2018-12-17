open Symbolic

let gen_id =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    !cpt

let sample (env, ef, natural_params) =
  let id = gen_id () in
  let env = (id, (ef, natural_params)) :: env in
  (env, Var id)


let analytic_update env exp =
  assert false (* XXX TODO XXX *)

let mc_update env exp =
  assert false (* XXX TODO XXX *)

let factor (env, exp) =
  begin match analytic_update env exp with
    | Some env' -> env'
    | None -> mc_update env exp
  end

(* let node infer model i = (env, o) where *)
(*     rec env, o =  model ([] fby env, i) *)


