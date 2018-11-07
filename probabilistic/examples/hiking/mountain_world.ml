open Gridworld

type mountain = { name: string }
type mountain_feature = mountain feature
type mountain_map = mountain map

let x = Wall
let h = Value { name = "Hill" }
let w = Value { name = "West" }
let e = Value { name = "East" }
let ___ = Empty

let grid =
  [|
    [| ___; ___; ___; ___; ___ |];
    [| ___;  x ; ___; ___; ___ |];
    [| ___;  x ;  w ;  x ;  e  |];
    [| ___; ___; ___; ___; ___ |];
    [|  h ;  h ;  h ;  h ;  h  |]
  |]

let utility_table feature =
  begin match feature with
  | Wall -> assert false
  | Value { name = "East" } -> 10.
  | Value { name = "West" } -> 1.
  | Value { name = "Hill" } -> -10.
  | Empty -> -0.1
  | _ -> assert false
  end

let utility map state action =
  utility_table (map.feature state.loc)

let print = print (fun r -> r.name)

let map = map_of_array grid
let (transition: mountain Gridworld.map -> Gridworld.state -> Gridworld.action -> Gridworld.state),
    (possible_actions: mountain Gridworld.map -> Gridworld.state -> Gridworld.action list) =
  make_world_deterministic []
let state_init = init_state (0, 1)

let draw = Gridworld.draw

let () =
  Graphics.open_graph " 400x400";
  Graphics.auto_synchronize false;
  ()
