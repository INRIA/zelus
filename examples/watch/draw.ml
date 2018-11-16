open Graphics
(*************** Graphical mess ***********************)
let pi = 3.1415

let start =
  open_graph " 800x600"; auto_synchronize false; set_line_width 2

let turn x0 y0 l xi yi angle =
  let x = xi *. (cos angle) -. (yi -. 100. *. l) *. (sin angle) in
  let y = xi *. (sin angle) +. (yi -. 100. *. l) *. (cos angle) +. (100. *. l) in
   x +. x0, y +. (y0 -. 100. *. l)


let draw_balance x0 y0 l angle thetac theta =
  let x00,y00 = turn x0 y0 l (-. 115.) 85. angle in
  set_color red;
  draw_circle (int_of_float x00) (int_of_float y00) 30;

  let theta = mod_float theta (2. *. pi) in
  let n = 4 in
  for i = 1 to 4 do
    let t = theta +. (float i) *. 2. *. pi /. (float n)  in
    let xi = -. 115. +. 30. *. (sin t) in
    let yi = 85. +. 30. *. (cos t) in
    let x,y = turn x0 y0 l xi yi angle in

    moveto (int_of_float x00) (int_of_float y00);
    lineto (int_of_float x) (int_of_float y);
  done;

  let t = theta +. (float 2) *. 2. *. pi /. (float n)  in
  let xi = -. 115. +. 20. *. (sin t) in
  let yi = 85. +. 20. *. (cos t) in
  let x,y = turn x0 y0 l xi yi angle in
  set_color blue;
  fill_circle (int_of_float x) (int_of_float y) 4;

  let t =
    if theta >= 0.0
    then min theta thetac
    else max theta (-. thetac)
  in

  let x00,y00 = turn x0 y0 l (-. 115.) 35. angle in

  let xi = -. 115. -. 23. *. (sin t) in
  let yi = 35. +. 23. *. (cos t) in
  let x,y = turn x0 y0 l xi yi angle in

  moveto (int_of_float x00) (int_of_float y00);
  lineto (int_of_float x) (int_of_float y);

  let tt1 = t +. 0.2 in
  let xt1i = -.115. -. 25. *. (sin tt1) in
  let yt1i = 35. +. 25. *. (cos tt1 ) in
  let xt1, yt1 = turn x0 y0 l xt1i yt1i angle in

  moveto (int_of_float x) (int_of_float y);
  lineto (int_of_float xt1) (int_of_float yt1);

  let tt2 = t -. 0.2 in
  let xt2i = -.115. -. 25. *. (sin tt2) in
  let yt2i = 35. +. 25. *. (cos tt2 ) in
  let xt2, yt2 = turn x0 y0 l xt2i yt2i angle in

  moveto (int_of_float x) (int_of_float y);
  lineto (int_of_float xt2) (int_of_float yt2);

  (* Draw escapement *)
  let te11 = t +. 0.8 in
  let xe11i = -. 115. +. 20. *. (sin te11) in
  let ye11i = 35. -. 20. *. (cos te11) in
  let xe11, ye11 = turn x0 y0 l xe11i ye11i angle in
  let te12 = t +. 0.4 in
  let xe12i = -. 115. +. 20. *. (sin te12) in
  let ye12i = 35. -. 20. *. (cos te12) in
  let xe12, ye12 = turn x0 y0 l xe12i ye12i angle in

  moveto (int_of_float x00) (int_of_float y00);
  lineto (int_of_float xe11) (int_of_float ye11);
  lineto (int_of_float xe12) (int_of_float ye12);

  let te21 = t -. 0.8 in
  let xe21i = -. 115. +. 20. *. (sin te21) in
  let ye21i = 35. -. 20. *. (cos te21) in
  let xe21, ye21 = turn x0 y0 l xe21i ye21i angle in
  let te22 = t -. 0.4 in
  let xe22i = -. 115. +. 20. *. (sin te22) in
  let ye22i = 35. -. 20. *. (cos te22) in
  let xe22, ye22 = turn x0 y0 l xe22i ye22i angle in

  moveto (int_of_float x00) (int_of_float y00);
  lineto (int_of_float xe21) (int_of_float ye21);
  lineto (int_of_float xe22) (int_of_float ye22)


let draw_spring x0 y0 l angle h0 h =
  let x00, y00 = turn x0 y0 l 35. 0. angle in
  set_color red;
  moveto (int_of_float x00) (int_of_float y00);
  draw_circle (int_of_float x00) (int_of_float y00) 50;
  let k = h *. 5.  in
  let n = 1000 in
  for i = 0 to n do
    let t = 2. *. k *. pi *. (float i) /. (float n) in
    let c = (float i) /. (float n) *. 50. in
    let xi = 35. +. cos t *. c in
    let yi = sin t *. c in
    let x,y = turn x0 y0 l xi yi angle in
    lineto (int_of_float x) (int_of_float y)
  done

let draw_hand x0 y0 l angle theta =
  let x00, y00 = turn x0 y0 l 35. 0. angle in
  let xi = 35. -. 65. *. (sin (theta +. pi)) in
  let yi =  -. 65. *. (cos (theta +. pi)) in
  let x,y = turn x0 y0 l xi yi angle in

  set_color black;
  fill_circle (int_of_float x00) (int_of_float y00) 5;
  moveto (int_of_float x00) (int_of_float y00);
  lineto (int_of_float x) (int_of_float y)


let draw_little_hand x0 y0 l angle theta =
  let x00, y00 = turn x0 y0 l 35. 0. angle in
  let xi = 35. -. 35. *. (sin (theta +. pi)) in
  let yi = -. 35. *. (cos (theta +. pi)) in
  let x,y = turn x0 y0 l xi yi angle in

  set_color black;
  moveto (int_of_float x00) (int_of_float y00);
  lineto (int_of_float x) (int_of_float y)

let draw_little_wheel x0 y0 l angle theta =
  let x00, y00 = turn x0 y0 l (-. 115.) (-. 5.) angle in
  set_color magenta;
  fill_circle (int_of_float x00) (int_of_float y00) 20;
  let n = 10 in
  for i = 1 to n do
    let t = theta +. 0.4 +. (float i) *. 2. *. pi /. (float n) in
    let xi = -. 115. +. -. 25. *. (sin t) in
    let yi = -. 5. -. 25. *. (cos t) in
    let x,y = turn x0 y0 l xi yi angle in
    moveto (int_of_float x00) (int_of_float y00);
    lineto (int_of_float x) (int_of_float y)
  done

let draw_big_wheel x0 y0 l angle theta =
  let x00, y00 = turn x0 y0 l 35. 0. angle in
  set_color green;
  fill_circle (int_of_float x00) (int_of_float y00) (120);
  let n = 60 in
  for i = 1 to n do
    let t = theta +. (float i) *. 2. *. pi /. (float n) in
    let xi = 35. -. 130. *. (sin t) in
    let yi = -. 130. *. (cos t) in
    let x,y = turn x0 y0 l xi yi angle in

    moveto (int_of_float x00) (int_of_float y00);
    lineto (int_of_float x) (int_of_float y)
  done


let draw_background x0 y0 l angle =
  let x00, y00 = turn x0 y0 l 0. 0. angle in
  set_line_width 2;
  set_color black;
  for i=0 to 20 do
    let xi = 0.0 in
    let yi = (float i) *. l *. 100. /. 20. in
    let x,y = turn x0 y0 l xi yi angle in
    draw_circle (int_of_float x) (int_of_float y) (int_of_float (100. *. l/. 30.))
  done;
  draw_circle (int_of_float x00) (int_of_float y00) 180;
  set_color white;
  fill_circle (int_of_float x00) (int_of_float y00) 179


let draw_mechanism x0 y0 l angle =
  let x00, y00 = turn x0 y0 l 35. 0. angle in
  (* Draw watch *)
  set_color white;
  fill_circle (int_of_float x00) (int_of_float y00) 70;
  set_color black;
  draw_circle (int_of_float x00) (int_of_float y00) 70;
  for i = 0 to 4 do
    let t = 2.*.pi *. (float i) /. 4. in
    let x1i = 35. +. 68. *. (cos t) in
    let y1i =  68. *. (sin t) in
    let x1, y1 = turn x0 y0 l x1i y1i angle in
    let x2i = 35. +. 72. *. (cos t) in
    let y2i = 72. *. (sin t) in
    let x2, y2 = turn x0 y0 l x2i y2i angle in

    moveto (int_of_float x1) (int_of_float y1);
    lineto (int_of_float x2) (int_of_float y2)
  done

let draw_system (x0, y0, l, angle, tc, t, h0, h, th, thl, twb, twl) =
  clear_graph ();
  draw_background x0 y0 l angle;
  draw_big_wheel x0 y0 l angle twb;
  draw_little_wheel x0 y0 l angle twl;
  draw_mechanism x0 y0 l angle;
  draw_balance x0 y0 l angle tc t;
  draw_spring x0 y0 l angle h0 h;
  draw_hand x0 y0 l angle th;
  draw_little_hand x0 y0 l angle thl;

  set_color black;
  fill_circle (int_of_float x0) (int_of_float y0) 5;

  synchronize ()

let play_tic () =
  sound 440 100

let play_toc () =
  sound 500 100


(* let event = ref 0 *)

(* let input () = *)
(*   if key_pressed() then begin *)
(*     match read_key() with *)
(*     | ' ' -> event := 1 *)
(*     | 'm' -> event := 2 *)
(*     | 'q' -> exit 0 *)
(*     | _ -> event := 0 *)
(*   end; *)
(*   let r = !event in *)
(*   event := 0; *)
(*   r *)


let input () =
  let rec myread v =
    if not (key_pressed ()) then v
    else myread (Some (read_key ()))
  in
  match myread None with
  | Some 'm' -> 2
  | Some ' ' -> 1
  | Some 'q' -> exit 0
  | _ -> 0
