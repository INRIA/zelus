(* test:
    ocaml -I +lablgtk2 lablgtk.cma gtkInit.cmo simplevector.ml a330.ml airtrafficgui.ml
 *)

let canvas_height = 800
let canvas_width  = 800

let color_lightblue = `NAME "#add8e6"
let color_black     = `NAME "#000000"
let color_orange    = `NAME "#ffa500"
let color_red       = `NAME "#ff0000"
let color_green     = `NAME "#00ff00"
let color_yellow    = `NAME "#ffff00"
let color_dimgray   = `NAME "#696969"
let color_ltgray    = `NAME "#898989"

let x_offset, y_offset = (canvas_width / 2), (canvas_height / 2)
let a330_scale = 75000.0
let max_pixels_per_mile = 15.0
let min_pixels_per_mile =  2.0

let pi = 4.0 *. atan 1.0
let sqr x = x *. x

let padd (x1, y1) (x2, y2) = (x1 + x2, y1 + y2)

(* 0: going right, 1: going down; 2: going left; 3: going up *)
let arrow_ps = [| (-5,-5); (-5,+5); (+5,+5); (+5,-5); (-5,-5) |]

let direction (x, y) (x', y') =
  if y == y'
  then (if x < x' then 0 else 2)
  else (if y < y' then 3 else 1)

let to_edge r dir (x, y) (x', y') =
  if dir = 0 then ((x + r, y), (x' - r, y))
  else if dir = 1 then ((x, y - r), (x, y' + r))
  else if dir = 2 then ((x - r, y), (x' + r, y))
  else ((x, y + r), (x, y' - r))

let scale_in_range scale =
  min (max min_pixels_per_mile scale) max_pixels_per_mile

let make_rect (x, y) (x', y') =
  Gdk.Rectangle.create
    ~x:(min x x') ~y:(min y y') ~width:(abs (x - x')) ~height:(abs (y - y'))

class model ~context ((x_off, y_off), r_alert, r_protected, delta_phi) =
  let text_layout = Pango.Layout.create context in
  object (self)
    (* {{{1 *)

    val x_off = x_off
    val y_off = y_off

    val mutable scale = 1.0 (* pixels per mile *)
    val r_alert = r_alert
    val r_protected = r_protected

    val mutable state = 0
    val mutable pstate = 0

    val mutable xr = 0.0
    val mutable yr = 0.0
    val mutable theta_r = 0.0
    val mutable v1 = 0.0
    val mutable v2 = 0.0
    val mutable t  = 0.0

    method update mst n_xr n_yr n_theta_r n_v1 n_v2 n_t =
      pstate <- state;
      state <- mst;
      xr <- n_xr;
      yr <- n_yr;
      theta_r <- n_theta_r;
      v1 <- n_v1;
      v2 <- n_v2;
      t  <- n_t;
      scale <- scale_in_range
                 (min (abs_float (float(x_offset - 20) /. n_xr))
                      (abs_float (float(y_offset - 20) /. n_yr)))

    method to_pix_len v = truncate (v *. scale)
    method to_pix (x, y) = (x_off + self#to_pix_len x,
                            y_off - self#to_pix_len y)

    method from_pix_len v = float(v) /. scale
    method from_pix (x, y) =
      (self#from_pix_len (x - x_off), self#from_pix_len (y - y_off))

    method put_text_toright (d : GDraw.drawable) (x, y) text =
      let _ = Pango.Layout.set_text text_layout text in
      let lwidth, lheight = Pango.Layout.get_pixel_size text_layout in
      d#put_layout ~x:x ~y:(y - lheight/2) ~fore:color_black text_layout

    method put_text (d : GDraw.drawable) (x, y) text =
      let _ = Pango.Layout.set_text text_layout text in
      let lwidth, lheight = Pango.Layout.get_pixel_size text_layout in
      d#put_layout ~x:(x - lwidth/2) ~y:(y - lheight/2) ~fore:color_black text_layout

    method draw_radii (x, y) in_alert in_protected (d : GDraw.drawable) =
      (* alert zone *)
      let xo, yo = self#to_pix (x -. r_alert, y +. r_alert) in
      let d_a = self#to_pix_len (r_alert *. 2.0) in

      d#set_foreground color_dimgray;
      d#arc ~x:xo ~y:yo ~width:d_a ~height:d_a ~filled:false
            ~start:0.0 ~angle:360.0 ();

      (* protected zone *)
      let xo, yo = self#to_pix (x -. r_protected, y +. r_protected) in
      let d_p = self#to_pix_len (r_protected *. 2.0) in

      if in_protected then begin
        d#set_foreground color_red;
        d#arc ~x:xo ~y:yo ~width:d_p ~height:d_p ~filled:true
              ~start:0.0 ~angle:360.0 ()
      end;
      d#set_foreground color_dimgray;
      d#arc ~x:xo ~y:yo ~width:d_p ~height:d_p ~filled:false
            ~start:0.0 ~angle:360.0 ();

    method draw_states (d : GDraw.drawable) =
      let st_r = 25 in
      let st_d = 2 * st_r in
      let st_sep = st_r + 20 in
      let xo, yo = st_sep + st_r + 5, canvas_height - st_sep - st_r - 5 in

      let draw_state name active (x, y) =
        if active
        then d#set_foreground color_red
        else d#set_foreground color_ltgray;
        d#arc ~x:(x - st_r) ~y:(y - st_r) ~width:st_d ~height:st_d
              ~filled:true ~start:0.0 ~angle:360.0 ();
        self#put_text d (x, y) name in

      let draw_arrow dir (x, y) =
        let x1, y1 = padd (x, y) arrow_ps.(dir) in
        let x2, y2 = padd (x, y) arrow_ps.(dir + 1) in
        d#line ~x:x ~y:y ~x:x1 ~y:y1;
        d#line ~x:x ~y:y ~x:x2 ~y:y2 in
      
      let draw_trans active p p' =
        let dir = direction p p' in
        let (x, y), (x', y') = to_edge st_r dir p p' in
        if active
        then d#set_foreground color_red
        else d#set_foreground color_ltgray;
        d#set_line_attributes ~width:2 ();
        d#line ~x:x ~y:y ~x:x' ~y:y';
        draw_arrow dir (x', y');
        d#set_line_attributes ~width:1 () in

      let cruisep   = (xo - st_sep, yo - st_sep) in
      let leftp     = (xo + st_sep, yo - st_sep) in
      let straightp = (xo + st_sep, yo + st_sep) in
      let rightp    = (xo - st_sep, yo + st_sep) in

      draw_trans (pstate = 0 && state = 1) cruisep   leftp;
      draw_trans (pstate = 1 && state = 2) leftp     straightp;
      draw_trans (pstate = 2 && state = 3) straightp rightp;
      draw_trans (pstate = 3 && state = 0) rightp    cruisep;

      draw_state "Cruise"   (state = 0) cruisep;
      draw_state "Left"     (state = 1) leftp;
      draw_state "Straight" (state = 2) straightp;
      draw_state "Right"    (state = 3) rightp

    method draw_t (d : GDraw.drawable) =
      let r = 30 in
      let di = 2 * r in
      let xo, yo = 170, canvas_height - 105 in
      let t_deg = t *. 360.0 in
      d#set_foreground color_dimgray;
      d#arc ~x:xo ~y:yo ~width:di ~height:di ~filled:true
            ~start:0.0 ~angle:360.0 ();
      d#set_foreground color_green;
      d#arc ~x:xo ~y:yo ~width:di ~height:di ~filled:true
            ~start:(90.0) ~angle:(-.t_deg) ();
      self#put_text d (xo + r, yo + di + 10) "t"

    method draw (d : GDraw.drawable) =
      let draw_velocity (x, y) v =
        let x_off = max 0 (truncate (2.0 *. scale)) in
        let y_off = max 0 (truncate (2.0 *. scale)) in
        self#put_text_toright d (x + x_off, y + y_off)
                                (Printf.sprintf "%0.0f mi/hr" v) in
      
      let distance = sqrt (sqr xr +. sqr yr) in
      let angle = atan2 yr xr in
      let in_alert = distance <= r_alert in
      let in_protected = distance <= r_protected in
      let xr_p, yr_p = self#to_pix (xr, yr) in

      (* draw scale *)
      self#put_text_toright d (27, 20) "10 miles";
      self#put_text_toright d (5,  37) "(aircraft not to scale)";
      d#set_foreground color_dimgray;
      d#set_line_attributes ~width:2 ();
      d#line ~x:30 ~y:10 ~x:(30 + self#to_pix_len 10.0) ~y:10;
      d#set_line_attributes ~width:1 ();

      (* draw radii around aircraft *)
      self#draw_radii (0.0, 0.0) in_alert in_protected d;
      (* self#draw_radii (xr, yr) false false d; *)

      (* draw a line between the aircraft *)
      d#set_line_attributes ~style:`ON_OFF_DASH ();
      d#set_foreground color_dimgray;
      d#line ~x:x_off ~y:y_off ~x:xr_p ~y:yr_p;
      d#set_line_attributes ~style:`SOLID ();
      let ldist = min 100.0 (distance /. 2.0) in
      let xl, yl = self#to_pix (ldist *. cos angle, ldist *. sin angle) in
      self#put_text_toright d (xl, yl) (Printf.sprintf "%0.0f mi" distance);

      let a330 = Simplevector.rescale A330.data (truncate(a330_scale /. scale)) in

      let angle_off = pi /. 2.0 in
      let display_angle = angle_off +.
        (if state = 1 then -. delta_phi
         else if state = 3 then delta_phi
         else 0.0) in

      (* draw aircraft 1 *)
      Simplevector.draw a330 d display_angle (x_off, y_off);
      draw_velocity (x_off, y_off) v1;

      (* draw aircraft 2 *)
      Simplevector.draw a330 d (display_angle -. theta_r) (xr_p, yr_p);
      draw_velocity (xr_p, yr_p) v2;

      (* graph value of t *)
      self#draw_t d;

      (* draw the state machine *)
      self#draw_states d;

      ()

    (* }}}1 *)
  end

class window model_params =
  (* {{{1 *)

  let w = GWindow.window
     ~title:"Airtraffic"
     ~width:canvas_width
     ~height:canvas_height
     ~resizable:false
     () in
  let pm1 = GDraw.pixmap
      ~width:canvas_width
      ~height:canvas_height
      () in
  let pm2 = GDraw.pixmap
      ~width:canvas_width
      ~height:canvas_height
      () in
  let evbox = GBin.event_box
      ~packing:w#add
      () in
  let fixed = GPack.fixed
      ~width:canvas_width
      ~height:canvas_height
      ~packing:evbox#add
      () in
  let context = w#misc#create_pango_context in
  let _ = context#set_font_description (Pango.Font.from_string "Sans 10") in

  (* }}}1 *)
  object (self)
    (* {{{1 *)

    val window = w
    val canvas = GMisc.pixmap
        pm1
        ~width:canvas_width
        ~height:canvas_height
        ~packing:(fixed#put ~x:0 ~y:0)
        ()
    val model = new model context#as_context model_params

    val mutable pixmap = (pm1, pm2)

    val mutable downxy = (None : (int * int) option)
    val mutable movexy = (None : (int * int) option)

    val mutable clicked = (None : ((float * float) * (float * float)) option)

    method draw_drag =
      let (live, _) = pixmap in
      let d = (live :> GDraw.drawable) in
      match downxy, movexy with
      | Some (x, y), Some (x', y') -> begin
            d#set_foreground color_yellow;
            d#line ~x:(x-5) ~y:y ~x:(x+5) ~y:y;
            d#line ~x:x ~y:(y-5) ~x:x ~y:(y+5);
            d#line ~x:x ~y:y ~x:x' ~y:y'
          end
      | _ -> ()

    method draw =
      let (live, offscreen) = pixmap in
      let d = (offscreen :> GDraw.drawable) in
      let (mx, my) = d#size in

      (* draw sky *)
      d#set_foreground color_lightblue;
      d#rectangle ~x:0 ~y:0 ~filled:true ~width:mx ~height:my ();

      model#draw d;

      pixmap <- (offscreen, live);
      self#draw_drag;

      window#misc#draw None

    method model = model

    method destroy () =
      GMain.Main.quit ()

    method show =
      window#show ();
      self#draw

    method private button_down ev =
      if GdkEvent.Button.button ev <> 1 then false
      else (downxy <- Some (int_of_float (GdkEvent.Button.x ev),
                            int_of_float (GdkEvent.Button.y ev));
            true)

    method private button_up ev =
      if GdkEvent.Button.button ev <> 1 then false
      else
        match downxy, movexy with
        | Some (x, y), Some (x', y') -> begin
              downxy <- None;
              movexy <- None;

              let (x, y)   = model#from_pix (x, y) in
              let (x', y') = model#from_pix (x', y') in
              let ang = atan2 (y -. y') (x' -. x) in
              let len = sqrt (sqr (x -. x') +. sqr (y -. y')) in
              clicked <- Some ((x, y), (ang, len));

              true
            end
        | _ -> false

    method private hold_drag ev =
      match downxy with
      | None -> false
      | Some (x, y) ->
          let x' = int_of_float (GdkEvent.Motion.x ev) in
          let y' = int_of_float (GdkEvent.Motion.y ev) in
          movexy <- Some (x', y');
          (* self#draw_drag; *)
          (* window#misc#draw (Some (make_rect (x, y) (x', y'))); *)
          true

    method where =
      let r =
        match clicked with
        | None -> (false, (0.0, 0.0), (0.0, 0.0))
        | Some ((x, y), al) -> (true, (x, -. y), al)
      in (clicked <- None; r)

    initializer
      ignore (window#connect#destroy   ~callback:self#destroy);
      ignore (evbox#event#connect#button_release ~callback:self#button_up);
      ignore (evbox#event#connect#button_press   ~callback:self#button_down);
      ignore (evbox#event#connect#motion_notify  ~callback:self#hold_drag);
      evbox#event#add [`BUTTON1_MOTION]

      (* }}}1 *)
  end

type airtraffic = window * model

(* 1 mile = scale pixels *)
(* r_alert and r_protected are in miles *)
let show d dtheta r_alert r_protected delta_phi =
  let w = new window ((x_offset, y_offset), r_alert, r_protected, delta_phi)
  in
  let _ = w#show in
  w, w#model

(* xr and yr are in miles
 * v1 and v2 are in miles/hour
 * t is in seconds
 * theta_r is in radians, measured anti-clockwise from the x-axis
 *)
let update (window, model) mst xr yr theta_r v1 v2 t =
  model#update mst xr yr theta_r v1 v2 t;
  window#draw

let sample ((window, model) : airtraffic) = window#where

(* Work around a problem in the compilation of fby TPB:20110319 *)
let state = ref (None : airtraffic option)
let showupdate (d, dtheta, r_alert, r_protected, delta_phi,
                mst, xr, yr, theta_r, v1, v2, t) =
  let st =
    match !state with
    | None -> let st = show d dtheta r_alert r_protected delta_phi in
              (state := Some st; st)
    | Some s -> s in
  update st mst xr yr theta_r v1 v2 t

let sample () =
    match !state with
    | None -> (false, (0.0, 0.0), (0.0, 0.0))
    | Some s -> sample s

(* test harness *)

let runtest () =
  let airtraffic = show 10.0 45.0 25.0 5.0 0.0 in
  update airtraffic 0 17.0 17.0 (-. 3.0 *. pi /. 4.0) 200.0 200.0 0.05;
  GMain.Main.main ()

