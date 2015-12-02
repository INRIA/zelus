
let box_size = 10
let half_box_size = box_size / 2

let width  = 400
let height = 600

let scale = float_of_int height
let x_off = (width / 2) - half_box_size
let y_off = 0

let hc h = truncate (h *. scale) - half_box_size + y_off
let background = Graphics.black

let clear () =
  Graphics.fill_rect 0 0 width height

let start () =
  Graphics.open_graph "";
  Graphics.resize_window width height;
  (* Graphics.auto_synchronize false; *)
  clear ()

let draw_box color h =
  Graphics.set_color color;
  Graphics.fill_rect x_off (hc h) box_size box_size

let draw_gravity color =
  Graphics.set_color color;
  Graphics.fill_rect 0 0 width 5

let show on last_h1 last_h2 h1 h2 =
  draw_gravity (if on then Graphics.yellow else background);
  draw_box background last_h1;
  draw_box background last_h2;
  draw_box Graphics.green h1;
  draw_box Graphics.red   h2
  (* Graphics.synchronize (); *)

let input () =
  let rec myread v =
    if not (Graphics.key_pressed ()) then v
    else myread (Some (Graphics.read_key ()))
  in
  match myread None with
  | Some _ -> true
  | _ -> false

let stop () =
  ignore (Graphics.read_key ());
  Graphics.close_graph ()

let _ = start ()

