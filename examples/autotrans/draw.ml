open Graphics

let pi = 3.14159265359

let radian_of_degree x = x *. pi /. 180.
let kmh_of_mph x = x *. 1.60934
let nm_of_ftlb x = x *. 1.35581
let ftlb_of_nm x = x /. 1.35581

let min_throttle, max_throttle = 0, 100
let min_brake, max_brake = 0, ((int_of_float (nm_of_ftlb (float_of_int 350))) + 1)
let min_speed, max_speed = 0, 242
let min_rpm, max_rpm = 600, 6000
let min_gear, max_gear = 1, 4

let draw_circ_counter x0 y0 r minv maxv label v =
  let centerx, centery = (x0 + r / 2), (y0 + r / 4) in
  let minangle, maxangle = -45, 225 in
  draw_arc centerx centery r r minangle maxangle;

  let angle_range = float_of_int (maxangle - minangle) in
  let val_ratio = abs_float (v -. float_of_int minv) /. (float_of_int (maxv - minv)) in
  let needleangle = (float_of_int maxangle) -. (val_ratio *. angle_range) in

  let xpos = int_of_float (0.9 *. (float_of_int r) *. (cos (radian_of_degree needleangle))) in
  let ypos = int_of_float (0.9 *. (float_of_int r) *. (sin (radian_of_degree needleangle))) in
  moveto centerx centery; lineto (centerx + xpos) (centery + ypos);

  set_font "-*-fixed-medium-r-semicondensed--15-*-*-*-*-*-iso8859-1";
  let mintext = string_of_int minv in
  let (minvsizex, minvsizey) = text_size mintext in
  moveto (centerx - 8 * r / 10 - minvsizex) (centery - 3 * r / 4); draw_string mintext;
  let maxtext = string_of_int maxv in
  let (maxvsizex, maxvsizey) = text_size maxtext in
  moveto (centerx + 8 * r / 10) (centery - 3 * r / 4); draw_string maxtext;


  set_font "-*-fixed-medium-r-semicondensed--15-*-*-*-*-*-iso8859-1";
  let (lsizex, lsizey) = text_size label in
  moveto (centerx - lsizex / 2) (centery - r + lsizey); draw_string label;
  let vtext = Printf.sprintf "%.2f" v in
  set_font "-*-fixed-medium-r-semicondensed--25-*-*-*-*-*-iso8859-1";
  let (vsizex, vsizey) = text_size vtext in
  moveto (centerx - vsizex / 2) (centery - r + lsizey + vsizey); draw_string vtext

let draw_throttle_counter = draw_circ_counter 225 350 100 min_throttle max_throttle "throttle (%)"
let draw_brake_counter = draw_circ_counter 475 350 100 min_brake max_brake "brake torque (N.m)"

let draw_speed_counter = draw_circ_counter 100 100 100 min_speed max_speed "speedometer (km/h)"
let draw_rpm_counter = draw_circ_counter 350 100 100 min_rpm max_rpm "tachometer (rpm)"
let draw_gear_counter = draw_circ_counter 600 100 100 min_gear max_gear "gear"

let draw_button x0 y0 w h text () =
  draw_rect x0 y0 w h;
  set_font "-*-fixed-medium-r-semicondensed--15-*-*-*-*-*-iso8859-1";
  let (tsizex, tsizey) = text_size text in
  moveto (x0 + (w / 2) - (tsizex / 2)) (y0 + h / 2 - tsizey / 2); draw_string text;
  (fun x y -> x > x0 && x < x0 + w && y > y0 && y < y0 + h)

let draw_throttle_zero_button = draw_button 50 350 50 50 "0"
let draw_throttle_max_button = draw_button 100 350 50 50 "max"
let draw_brake_zero_button = draw_button 650 350 50 50 "0"
let draw_brake_max_button = draw_button 700 350 50 50 "max"
let draw_throttle_minus_button = draw_button 50 300 50 50 "-"
let draw_throttle_plus_button = draw_button 100 300 50 50 "+"
let draw_brake_minus_button = draw_button 650 300 50 50 "-"
let draw_brake_plus_button = draw_button 700 300 50 50 "+"

(* ------------------------------ *)

let is_init = ref false

let pthrottle  = ref 0.
let pbrake     = ref 0.

let init () =
  open_graph "";
  set_window_title "Autotrans";
  resize_window 800 500;
  auto_synchronize false;
  is_init := true

let draw (throttle, brake_torque, rpm, gear, speed) =
  try
    let disp_speed = kmh_of_mph speed in

    if not !is_init then init();
    clear_graph ();

    draw_throttle_counter throttle;
    draw_brake_counter (nm_of_ftlb brake_torque);

    draw_speed_counter disp_speed;
    draw_rpm_counter rpm;
    draw_gear_counter gear;

    pthrottle := throttle;
    pbrake    := brake_torque;

    let throttle_zero_pressed = draw_throttle_zero_button () in
    let throttle_max_pressed = draw_throttle_max_button () in
    let brake_zero_pressed = draw_brake_zero_button () in
    let brake_max_pressed = draw_brake_max_button () in
    let throttle_plus_pressed = draw_throttle_plus_button () in
    let throttle_minus_pressed = draw_throttle_minus_button () in
    let brake_plus_pressed = draw_brake_plus_button () in
    let brake_minus_pressed = draw_brake_minus_button () in

    if button_down() then begin
      let (posx, posy) = mouse_pos () in

      if throttle_zero_pressed posx posy then
        pthrottle := float_of_int min_throttle;

      if throttle_max_pressed posx posy then
        pthrottle := float_of_int max_throttle;

      if brake_zero_pressed posx posy then
        pbrake := ftlb_of_nm (float_of_int min_brake);

      if brake_max_pressed posx posy then
        pbrake := ftlb_of_nm (float_of_int max_brake);

      if throttle_plus_pressed posx posy then
        pthrottle := min (!pthrottle +. 1.) (float_of_int max_throttle);

      if throttle_minus_pressed posx posy then
        pthrottle := max (!pthrottle -. 1.) (float_of_int min_throttle);

      if brake_plus_pressed posx posy then
        pbrake := min (!pbrake +. 10.) (ftlb_of_nm (float_of_int max_brake));

      if brake_minus_pressed posx posy then
        pbrake := max (!pbrake -. 10.) (ftlb_of_nm (float_of_int min_brake));
    end;

    synchronize ()
  with Graphic_failure s ->
    print_string "Exit."; print_newline (); exit 0

let get_inputs() = !pthrottle, !pbrake
