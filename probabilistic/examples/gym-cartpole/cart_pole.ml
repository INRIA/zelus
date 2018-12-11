open Openai_gym
open Gym_client
open Gym_j
open Gym_t

type instance_id = Gym_t.instance_id

type cart_observation = {
  cart_position: float;
  cart_velocity: float;
  pole_angle: float;
  pole_velocity: float;
}

type cart_action = Left | Right

let action_of_cart_action: cart_action -> action = begin
  fun a ->
    begin match a with
    | Left -> { action = 0 }
    | Right -> { action = 1 }
    end
end


let cart_observation_of_json : json -> cart_observation = begin
  fun observation ->
    let open Yojson.Basic.Util in
    let obs = List.map (to_float) (to_list observation) in
    begin match obs with
    | [cp; cv; pa; pv] ->
      { cart_position = cp;
        cart_velocity = cv;
        pole_angle = pa;
        pole_velocity = pv; }
    | _ -> assert false
    end
end

let cart_init: unit -> instance_id =  begin
  fun () -> env_create "CartPole-v1"
end

(* let () = *)
(*   Gym_client.env_monitor_start instance_id "/tmp/gym-results" true false *)

(* let () = *)
(*   Sys.set_signal *)
(*     Sys.sigint *)
(*     (Sys.Signal_handle *)
(*        (fun _ -> *)
(*           Format.eprintf "closing monitor@."; *)
(*           Gym_client.env_monitor_close instance_id; *)
(*           Format.eprintf "closing instance %s@." instance_id.instance_id; *)
(*           env_close instance_id; *)
(*           exit 0)) *)



let cart_reset: instance_id -> cart_observation = begin
  fun instance_id ->
    let obs = env_reset instance_id in
    cart_observation_of_json obs.observation
end

let cart_step: instance_id -> cart_action -> bool -> cart_observation * float * bool = begin
  fun instance_id action render ->
    let step_response = env_step instance_id (action_of_cart_action action) render in
    cart_observation_of_json step_response.step_observation,
    step_response.step_reward,
    step_response.step_done
end
