open Probzelus
open Ztypes

let with_graphics, max_pos =
  let with_graphics = ref true in
  let n = ref 10 in
  Arg.parse
    [ "-nox", Arg.Clear with_graphics, "Disable the graphics interface";
      "-n", Arg.Set_int n, "Set the size of the map"; ]
    (fun _ -> ()) "options:";
  !with_graphics, !n - 1

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


let init_graph max_pos =
  let size = " "^(string_of_int ((max_pos + 1) * 50))^"x100" in
  Graphics.open_graph size;
  Graphics.set_window_title "SLAM";
  Graphics.auto_synchronize false;
  Format.printf "Press in the graphic window:@.";
  Format.printf "- 'l' to go left@.";
  Format.printf "- 'r' to go right@.";
  Format.printf "- 'q' to quit@.";
  Format.printf "- any other key for automatic control@."

let clear () =
  Graphics.synchronize ();
  Graphics.clear_graph ()

let wait_event () =
  let c = Graphics.read_key () in
  begin match c with
  | 'l' ->  -1
  | 'r' ->  1
  | 'q' -> exit 0
  | _ -> 0
  end
  (* ignore (Graphics.read_key ()) *)

let width = 50
let height = 50

let draw_bot x obs =
  Graphics.set_color (Graphics.blue);
  Graphics.fill_circle (x * width + width / 2) (3 * height / 2) 10;
  if obs then Graphics.set_color (Graphics.white)
  else Graphics.set_color (Graphics.black);
  Graphics.fill_circle (x * width + width / 2) (3 * height / 2) 5


let draw_position_dist d =
  for x = 0 to max_pos do
    let p = exp (Distribution.score (d, x)) in
    if p > 0. then begin
      Graphics.set_color (Graphics.red);
      Graphics.fill_circle
        (x * width + width / 2) (height / 2)
        (1 + int_of_float (10. *. p))
    end
  done

let draw_map_dist map_dist =
  let mw = Array.map
    (fun d ->
      let d_true, d_false = Distribution.split d in
      let n_t, n_f = mean_float d_true, mean_float d_false in
      n_t /. (n_t +. n_f))
    (Distribution.split_array map_dist)
  in
  Array.iteri (fun i w ->
    let gray = int_of_float (w *. 255.) in
    Graphics.set_color (Graphics.rgb gray gray gray);
    Graphics.fill_rect (i * width)  0  width height)
    mw

let draw_map_dist_ds map_dist =
  let mw = Array.map
    (fun d -> Distribution.mean_float d)
    (Distribution.split_array map_dist)
  in
  Array.iteri (fun i w ->
    let gray = int_of_float (w *. 255.) in
    Graphics.set_color (Graphics.rgb gray gray gray);
    Graphics.fill_rect (i * width)  0  width height)
    mw

let draw_map m =
  Array.iteri (fun i b ->
    if b then Graphics.set_color (Graphics.white)
    else Graphics.set_color (Graphics.black);
    Graphics.fill_rect (i * width)  height  width height)
    m

let random n theta =
  Array.init n
    (fun _ -> Distribution.draw (Distribution.bernoulli theta))

let () =
  if with_graphics then init_graph max_pos

let input =
  if with_graphics then
    wait_event
  else
    (fun () -> 0)

let output =
  if with_graphics then
    (fun real_map real_x obs map_dist pos_dist ->
       draw_map real_map;
       draw_bot real_x obs;
       draw_map_dist map_dist;
       draw_position_dist pos_dist;
       clear ())
  else
    (fun real_map real_x obs map_dist pos_dist ->
       print_map_dist map_dist)

let output_ds =
  if with_graphics then
    (fun real_map real_x obs map_dist pos_dist ->
       draw_map real_map;
       draw_bot real_x obs;
       draw_map_dist_ds map_dist;
       draw_position_dist pos_dist;
       clear ())
  else
    (fun _ -> assert false)
    (* (fun real_map real_x obs map_dist pos_dist -> *)
    (*    print_map_dist map_dist) *)

let float_of_bool b =
  if b then 1. else 0.

let color_diff expected actual =
  let b = actual > 0.5 in
  if expected = b then 0. else 1.

let error (map, x) map_d d_x =
  let len = Array.length map in
  let e = ref ((float x -. Distribution.mean_int d_x) ** 2.) in
  for i = 0 to len - 1 do
    e := !e +. (float_of_bool map.(i) -. mean_float map_d.(i)) ** 2.
  done;
  !e
