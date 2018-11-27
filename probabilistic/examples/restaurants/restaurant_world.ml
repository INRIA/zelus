open Gridworld

type restaurant = { name : string }
type restaurant_feature = restaurant feature
type restaurant_map = restaurant map

let w = Wall
let ___ = Empty
let dn = Value { name = "DN" }
let ds = Value { name = "DS" }
let v = Value { name = "Veg" }
let n = Value { name = "Noodle" }

let grid =
  [|
    [| w  ; w  ; w  ; w  ;  v ; w   |];
    [| w  ; w  ; w  ; ___; ___; ___ |];
    [| w  ; w  ; dn ; ___; w  ; ___ |];
    [| w  ; w  ; w  ; ___; w  ; ___ |];
    [| w  ; w  ; w  ; ___; ___; ___ |];
    [| w  ; w  ; w  ; ___; w  ; n   |];
    [| ___; ___; ___; ___; w  ; w   |];
    [| ds ; w  ; w  ; ___; w  ; w   |];
  |]



let utility_table feature =
  begin match feature with
  | Wall -> assert false
  | Value { name = "DN" } -> 1.
  | Value { name = "DS" } -> 1.
  | Value { name = "Veg" } -> 3.
  | Value { name = "Noodle" } -> 2.
  | Empty -> -0.1
  | _ -> assert false
  end

let utility map state action =
  utility_table (map.feature state.loc)

let print = print (fun r -> r.name)


let map = map_of_array grid
let (transition: restaurant_map -> state -> action -> state),
    (possible_actions: restaurant_map -> state -> action list) =
  make_world_deterministic [ ]
let state_init = init_state (3, 1)

let draw = Gridworld.draw

let () =
  Graphics.open_graph " 400x400";
  Graphics.auto_synchronize false;
  ()

let debug_state =
  let tbl = Hashtbl.create 7 in
  fun state ->
  let (x, y) = state.loc in
  if not (Hashtbl.mem tbl (x, y)) then begin
    Hashtbl.add tbl (x, y) ();
    Format.printf "(%d, %d)@." x y;
  end;
  state

(** Tests *)

(* let () = *)
(*   let world = deterministic_mdp in *)
(*   print (fun r -> r.name) world.map; *)
(*   let possible_actions = world.possible_actions world.map in *)
(*   Format.printf "Possible actions = [ "; *)
(*   List.iter *)
(*     (fun a -> Format.printf "%s " (string_of_action a)) *)
(*     possible_actions; *)
(*   Format.printf "]@."; *)
(*   () *)

(* (\** Tests *\) *)

(* let () = *)
(*   let world = deterministic_mdp in *)
(*   print (fun r -> r.name) world.map; *)
(*   let possible_actions = world.possible_actions world.map in *)
(*   Format.printf "Possible actions = [ "; *)
(*   List.iter *)
(*     (fun a -> Format.printf "%s " (string_of_action a)) *)
(*     possible_actions; *)
(*   Format.printf "]@."; *)
(*   () *)
