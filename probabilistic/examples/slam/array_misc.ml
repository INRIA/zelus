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

let split n d =
  begin match d with
  | Dist_sampler (draw, score) -> assert false
  | Dist_support support ->
      Array.init n
        (fun i ->
           let p_true, p_false =
             List.fold_left
               (fun (p_true, p_false) (b, p) ->
                  if b.(i) then (p_true +. p, p_false)
                  else (p_true, p_false +. p))
               (0., 0.) support
           in
           Dist_support [ (true, p_true); (false, p_false) ])
  end

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
  Graphics.open_graph " 550x50";
  Graphics.auto_synchronize false

let clear () =
  Graphics.synchronize ();
  Graphics.clear_graph ()

let wait_event () =
  ignore (Graphics.read_key ())

let width = 50
let height = 50
    
let draw_bot x =
  Graphics.set_color (Graphics.red);
  Graphics.fill_circle (x * width + width / 2) (height / 2) 10

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
    mw;


