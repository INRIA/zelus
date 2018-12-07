open Gym_http
open Gym_client
open Gym_j
open Gym_t

let copysign = copysign

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

let instance_id = env_create "CartPole-v1"

let cart_reset: unit -> cart_observation = begin
  fun () -> cart_observation_of_json (env_reset instance_id).observation
end

let cart_step: cart_action -> bool -> cart_observation * float = begin
  fun action render ->
    let step_response = env_step instance_id (action_of_cart_action action) render in
    cart_observation_of_json step_response.step_observation, step_response.step_reward
end

let print_cart_observation obs =
  Format.printf "Cart Position: %f Cart Velocity: %f@." obs.cart_position obs.cart_velocity;
  Format.printf "Pole Angle: %f    Pole Velocity: %f@." obs.pole_angle obs.pole_velocity
