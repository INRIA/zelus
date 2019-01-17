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


let () =
  Graphics.open_graph " 550x100";
  Graphics.auto_synchronize false

let clear () =
  Graphics.synchronize ();
  Graphics.clear_graph ()

let wait_event () =
  ignore (Graphics.read_key ())

let width = 50
let height = 50

let draw_position x =
  Graphics.set_color (Graphics.red);
  Graphics.fill_circle (x * width + width / 2) (height / 2) 10

let draw_position_dist d =
  match d with
  | Distribution.Dist_sampler _ -> assert false
  | Distribution.Dist_support support ->
      List.iter
        (fun (x, p) ->
           Graphics.set_color (Graphics.blue);
           Graphics.draw_circle
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

let draw_pos_dist pd =
  match pd with
  | Dist_sampler _  -> assert false
  | Dist_support sup ->
    List.iter (fun (x, p) ->
      Graphics.set_color (Graphics.red);
      let w = int_of_float (p *. 10.) in
      Graphics.fill_circle (x * width + width / 2) (height / 4) w)
      sup
      
let random n theta =
  Array.init n
    (fun _ -> Distribution.draw (Distribution.bernoulli theta))
