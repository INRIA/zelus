open Ztypes

let ignore = ignore

let length = Array.length
let make = Array.make
let set = Array.set
let get = Array.get               let ( ^^ ) a i = get a i
let map = Array.map
let mapi f = Array.mapi (fun i x -> f (i, x))
let iter = Array.iter
let to_list = Array.to_list
let of_list = Array.of_list

let ( +: ) a1 a2 = Array.map2 ( +. ) a1 a2
let ( -: ) a1 a2 = Array.map2 ( -. ) a1 a2
let ( *: ) a1 a2 = Array.map2 ( *. ) a1 a2
let ( /: ) a1 a2 = Array.map2 ( /. ) a1 a2

let ( +.: ) x a = Array.map (( +. ) x) a
let ( -.: ) x a = Array.map (( -. ) x) a
let ( *.: ) x a = Array.map (( *. ) x) a
let ( /.: ) x a = Array.map (( /. ) x) a

let ( +:. ) a y = Array.map (fun x -> ( +. ) x y) a
let ( -:. ) a y = Array.map (fun x -> ( -. ) x y) a
let ( *:. ) a y = Array.map (fun x -> ( *. ) x y) a
let ( /:. ) a y = Array.map (fun x -> ( /. ) x y) a

let norm a = sqrt (Array.fold_left (fun acc x -> acc +. (x *. x)) 0. a)

type 'a map_state = {
  map_states : 'a array
}

let mapc n (Hybrid {alloc; step; reset}) =
  let alloc () = { map_states = Array.init n (fun _ -> alloc ()) } in
  let reset state = Array.iter reset state.map_states in
  let step { map_states } inputs =
    Array.map2 (fun s i -> step s i) map_states inputs in
  Hybrid { alloc; reset; step }

let mapd n (Node {alloc; step; reset}) =
  let alloc () = { map_states = Array.init n (fun _ -> alloc ()) } in
  let reset state = Array.iter reset state.map_states in
  let step { map_states } inputs =
    Array.map2 (fun s i -> step s i) map_states inputs in
  Node { alloc; reset; step }
