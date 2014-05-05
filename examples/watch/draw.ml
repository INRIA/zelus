open Graphics
(*************** Graphical mess ***********************)
let pi = 3.1415

let start =
  open_graph ""; auto_synchronize false; set_line_width 2

let x0 = 175.
let y0 = 300.

let draw_balance thetac theta =
  set_color red;
  draw_circle (int_of_float x0) (int_of_float (y0 +.50.)) 30;

  let theta = mod_float theta (2. *. pi) in
  let n = 4 in
  for i = 1 to 4 do
    let t = theta +. (float i) *. 2. *. pi /. (float n)  in
    let x = x0 +. 30. *. (sin t) in
    let y = y0 +. 50. +. 30. *. (cos t) in
    moveto (int_of_float x0) (int_of_float (y0 +. 50.));
    lineto (int_of_float x) (int_of_float y);
  done;
  let t = theta +. (float 2) *. 2. *. pi /. (float n)  in
  let x = x0 +. 20. *. (sin t) in
  let y = y0 +. 50. +. 20. *. (cos t) in
  set_color blue;
  fill_circle (int_of_float x) (int_of_float y) 4;

  let t =
    if theta >= 0.0
    then min theta thetac
    else max theta (-. thetac)
  in


  let x = x0 -. 23. *. (sin t) in
  let y = y0 +. 23. *. (cos t) in

  moveto (int_of_float x0) (int_of_float y0);
  lineto (int_of_float x) (int_of_float y);

  let tt1 = t +. 0.2 in
  let xt1 = x0 -. 25. *. (sin tt1) in
  let yt1 = y0 +. 25. *. (cos tt1 ) in

  moveto (int_of_float x) (int_of_float y);
  lineto (int_of_float xt1) (int_of_float yt1);

  let tt2 = t -. 0.2 in
  let xt2 = x0 -. 25. *. (sin tt2) in
  let yt2 = y0 +. 25. *. (cos tt2 ) in

  moveto (int_of_float x) (int_of_float y);
  lineto (int_of_float xt2) (int_of_float yt2);

  (* Draw escapement *)
  let te1 = t +. 0.8 in
  let xe1 = x0 +. 20. *. (sin te1) in
  let ye1 = y0 -. 20. *. (cos te1 ) in
  let te1' = t +. 0.4 in
  let xe1' = x0 +. 20. *. (sin te1') in
  let ye1' = y0 -. 20. *. (cos te1') in

  moveto (int_of_float x0) (int_of_float y0);
  lineto (int_of_float xe1) (int_of_float ye1);
  lineto (int_of_float xe1') (int_of_float ye1');

  let te2 = t -. 0.8 in
  let xe2 = x0 +. 20. *. (sin te2) in
  let ye2 = y0 -. 20. *. (cos te2) in
  let te2' = t -. 0.4 in
  let xe2' = x0 +. 20. *. (sin te2') in
  let ye2' = y0 -. 20. *. (cos te2') in

  moveto (int_of_float x0) (int_of_float y0);
  lineto (int_of_float xe2) (int_of_float ye2);
  lineto (int_of_float xe2') (int_of_float ye2')


let draw_spring h0 h =
  set_color red;
  moveto (int_of_float (x0+.150.)) (int_of_float (y0 -. 35.));
  draw_circle (int_of_float (x0+.150.)) (int_of_float (y0 -. 35.)) 50;
  let k = h *. 5.  in
  let n = 1000 in
  for i = 0 to n do
    let t = 2. *. k *. pi *. (float i) /. (float n) in
    let c = (float i) /. (float n) *. 50. in
    let x = x0 +. 150. +. cos t *. c in
    let y = y0 -. 35. +. sin t *. c in
    lineto (int_of_float x) (int_of_float y)
  done

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
  lineto (int_of_float (x0+.150.)) (int_of_float (y0 -. 35. -. 72.))

let draw_digital h m s =
  set_color black;
  set_text_size 50;
  moveto (int_of_float (x0 +. 125.)) (int_of_float (y0 +. 50.));
  draw_string ((string_of_int h)^" : "^(string_of_int m)^" : "^(string_of_int s))



let draw_system l tc t h0 h th thl twb twl hh mm ss =
  clear_graph ();
  draw_big_wheel twb;
  draw_little_wheel twl;
  draw_mechanism ();
  draw_balance tc t;
  draw_spring h0 h;
  draw_hand th;
  draw_little_hand thl;
  draw_digital hh mm ss;
  synchronize ()

let event = ref false


let play_tic () =
  sound 440 100

let play_toc () =
  sound 500 100


let input () =
  if key_pressed() then begin
    if read_key() = ' ' then event := true
  end;
  let r = !event in
  event := false;
  r
