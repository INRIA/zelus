(* Author: François Bidet *)

let leader_color = Graphics.rgb 255 105 180
let interior_color = Graphics.rgb 255 255 0
let rear_color = Graphics.rgb 255 0 0
let merging_color = Graphics.rgb 0 255 0

let separator_width = 0.15 (* 15 cm *)
let separator_length = 3. (* 3m *)
let separator_gap = 10. (* 10m *)
let separator_period = separator_length +. separator_gap
let separator_y = 1.75

let margin = 10

let x_max = 100. (* x_min is the position of the rear vehicle*)

let y_min = -1.75 (* first lane center around 0 *)
let y_max = 5.25

let zoom = 10.0

let vehicle_length = Constants.l
let vehicle_width = 1.

let to_pixel x = int_of_float (zoom *. x)

let x_resolution = (2 * margin) + (to_pixel x_max)
let y_resolution = (2 * margin) + (to_pixel (y_max -. y_min) )

let to_coord_x x =
  margin + (to_pixel x)

let to_coord_y y =
  margin + (to_pixel (y -. y_min))

let to_coord p =
  let (x,y) = p in
  (to_coord_x x, to_coord_y y)

let add p1 p2 =
  let (x1,y1) = p1 in
  let (x2,y2) = p2 in
  (x1+.x2, y1+.y2)

let opposite p =
  let (x,y) = p in
  (-. x, -. y)

let get_poly p v1 v2 =
  [| (add p v2); (add (add p v2) v1); (add (add p (opposite v2)) v1); (add p (opposite v2)) |]

let get_poly_vehicle vehicle =
  let l = vehicle_length in
  let w = vehicle_width /. 2. in
  let (x,y,phi,_,_,_) = vehicle in
  let v1 = (l *. (cos phi), l *. (sin phi)) in
  let v2 = (-. w *. (sin phi), w *. (cos phi)) in
  let p = (x, y) in
  get_poly p v1 v2

let correction poly x0=
  let p = Array.map (add (-.x0,0.)) poly in
  Array.map to_coord p

let draw_vehicle x x_ref color =
  let poly = correction (get_poly_vehicle x) x_ref in
  Graphics.set_color color;
  Graphics.fill_poly poly;
  Graphics.set_color Graphics.black;
  Graphics.draw_poly poly

let draw_vehicles x_ref x_rear x_int x_lead x_merg =
  (* rear *)
  draw_vehicle x_rear x_ref rear_color;
  (* interior *)
  draw_vehicle x_int x_ref interior_color;
  (* leader *)
  draw_vehicle x_lead x_ref leader_color;
  (* merging *)
  draw_vehicle x_merg x_ref merging_color;
  ()

let get_poly_separator x =
  let l = separator_length in
  let w = separator_width /. 2. in
  let y = separator_y in
  let v1 = (l,0.) in
  let v2 = (0.,w) in
  let p = (x,y) in
  get_poly p v1 v2

let rec draw_separator x x_ref =
  if x -. x_ref < x_max then
    let poly = correction (get_poly_separator x) x_ref in
    Graphics.fill_poly poly;
    draw_separator (x +. separator_period) x_ref

let draw_separators x_ref =
  Graphics.set_color Graphics.black;
  let offset = mod_float x_ref separator_period in
  draw_separator (x_ref -. offset) x_ref


let draw t x_rear x_int x_lead x_merg =
  Graphics.clear_graph ();
  let (x_ref, _,_,_,_,_) = x_rear in
  draw_separators x_ref;
  draw_vehicles x_ref x_rear x_int x_lead x_merg;
  ()

let init_graph () =
  Graphics.open_graph "";
  Graphics.resize_window x_resolution y_resolution;
  Graphics.clear_graph ();
  ()


let () = init_graph ()
