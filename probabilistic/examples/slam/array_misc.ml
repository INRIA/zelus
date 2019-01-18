type 'a t = 'a array

let get a i =
  a.(i)

let set a i v =
  let a' = Array.copy a in
  a'.(i) <- v;
  a'

let of_list = Array.of_list

let make = Array.make

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
  match d with
  | Distribution.Dist_sampler _ -> assert false
  | Distribution.Dist_support support ->
      List.iter
        (fun (x, p) ->
           Graphics.set_color (Graphics.red);
           Graphics.fill_circle
             (x * width + width / 2) (height / 2)
             (1 + int_of_float (10. *. p)))
        support
	
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

let draw_map m =
  Array.iteri (fun i b ->
    if b then Graphics.set_color (Graphics.white)
    else Graphics.set_color (Graphics.black);
    Graphics.fill_rect (i * width)  height  width height)
    m
    
let random n theta =
  Array.init n
    (fun _ -> Distribution.draw (Distribution.bernoulli theta))
