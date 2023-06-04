open Graphics
(*************** Graphical mess ***********************)
let pi = 3.1415

let start =
  open_graph ""; auto_synchronize false; set_line_width 2

let x0 = 175.
let y0 = 300.

let draw_pendulum l thetac theta =
  (* Draw pendulum *)
  let x = x0 +. 100. *. l *. (sin theta) in
  let y = y0 -. 100. *. l *. (cos theta) in

  set_color blue;
  moveto (int_of_float x0) (int_of_float y0);
  lineto (int_of_float x) (int_of_float y);
  fill_circle (int_of_float x) (int_of_float y) 15;

  (* Draw tip *)
  let xt = x0 -. 20. *. (sin theta) in
  let yt = y0 +. 20. *. (cos theta) in
  moveto (int_of_float x0) (int_of_float y0);
  lineto (int_of_float xt) (int_of_float yt);
  fill_circle (int_of_float xt) (int_of_float yt) 4;

  (* Draw escapement *)
  let te1 = theta +. 2. *. thetac in
  let xe1 = x0 +. 20. *. (sin te1) in
  let ye1 = y0 -. 20. *. (cos te1 ) in
  let te1' = theta +. thetac in
  let xe1' = x0 +. 20. *. (sin te1') in
  let ye1' = y0 -. 20. *. (cos te1') in

  moveto (int_of_float x0) (int_of_float y0);
  lineto (int_of_float xe1) (int_of_float ye1);
  lineto (int_of_float xe1') (int_of_float ye1');

  let te2 = theta -. 2. *. thetac in
  let xe2 = x0 +. 20. *. (sin te2) in
  let ye2 = y0 -. 20. *. (cos te2) in
  let te2' = theta -. thetac in
  let xe2' = x0 +. 20. *. (sin te2') in
  let ye2' = y0 -. 20. *. (cos te2') in

  moveto (int_of_float x0) (int_of_float y0);
  lineto (int_of_float xe2) (int_of_float ye2);
  lineto (int_of_float xe2') (int_of_float ye2')

let draw_weights h0 h =
  (* Draw main weight *)
  let x = x0 +. 150. +. 18.  in
  let y = y0 -. 35. in

  set_color red;
  moveto (int_of_float x) (int_of_float y);
  lineto (int_of_float x) (int_of_float (100. *. h));
  fill_rect (int_of_float (x -. 5.)) (int_of_float (100. *. h)) 10 20;

  (* Draw secondary weigh *)
  let x = x0 +. 150. -. 18.  in
  let y = y0 -. 35. in
  moveto (int_of_float x) (int_of_float y);
  lineto (int_of_float x) (int_of_float (100. *. (h0 -. h)));
  fill_rect (int_of_float (x -. 5.)) (int_of_float (100. *. (h0 -. h))) 10 20

let draw_hand theta =
  let x = x0 +. 150. -. 65. *. (sin (theta +. pi)) in
  let y = (y0 -. 35.) -. 65. *. (cos (theta +. pi)) in

  set_color black;
  fill_circle (int_of_float (x0 +. 150.)) (int_of_float (y0 -. 35.)) 5;
  moveto (int_of_float (x0 +. 150.)) (int_of_float (y0 -. 35.));
  lineto (int_of_float x) (int_of_float y)


let draw_little_hand theta =
  let x = x0 +. 150. -. 35. *. (sin (theta +. pi)) in
  let y = (y0 -. 35.) -. 35. *. (cos (theta +. pi)) in

  set_color black;
  moveto (int_of_float (x0 +. 150.)) (int_of_float (y0 -. 35.));
  lineto (int_of_float x) (int_of_float y)

let draw_little_wheel theta =
  set_color magenta;
  fill_circle (int_of_float x0) (int_of_float (y0 -. 40.)) 20;
  let n = 10 in
  for i = 1 to n do
    let t = theta +. 0.4 +. (float i) *. 2. *. pi /. (float n) in
    let x = x0 -. 25. *. (sin t) in
    let y = (y0 -. 40.) -. 25. *. (cos t) in

    moveto (int_of_float x0) (int_of_float (y0 -. 40.));
    lineto (int_of_float x) (int_of_float y)
  done

let draw_big_wheel theta =
  set_color green;
  fill_circle (int_of_float (x0+.150.)) (int_of_float (y0 -. 35.)) (120);
  let n = 60 in
  for i = 1 to n do
    let t = theta +. (float i) *. 2. *. pi /. (float n) in
    let x = x0 +. 150. -. 130. *. (sin t) in
    let y = (y0 -. 35.) -. 130. *. (cos t) in

    moveto (int_of_float (x0+.150.)) (int_of_float (y0 -. 35.));
    lineto (int_of_float x) (int_of_float y)
  done

let draw_mechanism () =
  (* Draw watch *)
  set_color white;
  fill_circle (int_of_float (x0+.150.)) (int_of_float (y0 -. 35.)) 70;
  set_color black;
  draw_circle (int_of_float (x0+.150.)) (int_of_float (y0 -. 35.)) 70;
  moveto (int_of_float (x0+.150. +. 68.)) (int_of_float (y0 -. 35.));
  lineto (int_of_float (x0+.150. +. 72.)) (int_of_float (y0 -. 35.));
  moveto (int_of_float (x0+.150. -. 68.)) (int_of_float (y0 -. 35.));
  lineto (int_of_float (x0+.150. -. 72.)) (int_of_float (y0 -. 35.));
  moveto (int_of_float (x0+.150.)) (int_of_float (y0 -. 35. +. 68.));
  lineto (int_of_float (x0+.150.)) (int_of_float (y0 -. 35. +. 72.));
  moveto (int_of_float (x0+.150.)) (int_of_float (y0 -. 35. -. 68.));
  lineto (int_of_float (x0+.150.)) (int_of_float (y0 -. 35. -. 72.));

  (* Draw weights wheel *)
  set_color red;
  fill_circle (int_of_float (x0+.150.)) (int_of_float (y0 -. 35.)) 20


let draw_digital h m s =
  set_color black;
  set_text_size 50;
  moveto (int_of_float (x0 +. 125.)) (int_of_float (y0 +. 50.));
  draw_string ((string_of_int h)^" : "^(string_of_int m)^" : "^(string_of_int s))



let draw_system (l, tc, t, h0, h, th, thl, twb, twl, hh, mm, ss) =
  clear_graph ();
  draw_big_wheel twb;
  draw_little_wheel twl;
  draw_mechanism ();
  draw_pendulum l tc t;
  draw_weights h0 h;
  draw_hand th;
  draw_little_hand thl;
  draw_digital hh mm ss;
  synchronize ()

let play_tic () =
  sound 440 100

let play_toc () =
  sound 500 100

(* let event = ref false *)

(* let input () = *)
(*   if key_pressed() then begin *)
(*     if read_key() = ' ' then event := true *)
(*   end; *)
(*   let r = !event in *)
(*   event := false; *)
(*   r *)


let input () =
  let rec myread v =
    if not (key_pressed ()) then v
    else myread (Some (read_key ()))
  in
  match myread None with
  | Some ' ' -> true
  | Some 'q' -> exit 0
  | _ -> false
