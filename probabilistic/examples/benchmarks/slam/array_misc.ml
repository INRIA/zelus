open Ztypes

let sensor_noise = 0.1
let wheel_noise = 0.1

let max_pos = 50

type 'a t = 'a array

let get a i =
  a.(i)

(* let set a i v = *)
(*   a.(i) <- v *)

let set a i v =
  let a = Array.copy a in
  a.(i) <- v;
  a

let of_list = Array.of_list

let make = Array.make

let ini n (Cnode f)  =
  let alloc () = f.alloc () in
  let reset state = f.reset state in
  let copy src dst = f.copy src dst in
  let step state (proba, arg) =
    Array.init n (fun i -> f.step state (proba, i))
  in
  Cnode { alloc; reset; copy; step; }


open Distribution

let print to_string a =
  Format.printf "[ @[";
  Array.iter
    (fun x -> Format.printf "%s;@ " (to_string x))
    a;
  Format.printf "@]]@."

let print_map_dist a =
  print
    (fun d ->
       let d_true, d_false = Distribution.split d in
       "("^(string_of_float (mean_float d_true))^", "
       ^(string_of_float (mean_float d_false))^")")
    (Distribution.split_array a)


let random n theta =
  Array.init n
    (fun _ -> Distribution.draw (Distribution.bernoulli theta))

let float_of_bool b =
  if b then 1. else 0.

let error (map, x) map_d d_x =
  let len = Array.length map in
  let e = ref ((float x -. Distribution.mean_int d_x) ** 2.) in
  for i = 0 to len - 1 do
    e := !e +. (float_of_bool map.(i) -. mean_float map_d.(i)) ** 2.
  done;
  !e

let print_bool b =
  print_string (if b then "true" else "false")

let print_map map =
  Array.iter (fun b -> print_bool b;  print_string ", ") map
