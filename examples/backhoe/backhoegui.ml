(* test: ocaml -I +lablgtk2 lablgtk.cma gtkInit.cmo backhoegui.ml *)

(*
 * Author: T. Bourke (INRIA / ENS)
 *
 * This example and user interface is a port of an earlier version in Tcl/Tk
 * written by T. Bourke (UNSW / NICTA) for a course on real-time systems
 * (COMP3241/9245) at UNSW run in part by Arcot Sowmya.
 *
 * The example is based on information from:
 *  - `How Caterpillar Backhoe Loaders Work', Marshall Brain, Tom Harris
 *    http://www.howstuffworks.com/backhoe-loader.htm
 *  - John Deere 110TLB and 310G Backhoe loaders
 *)

let canvas_height = 600
let canvas_width  = 800

let color_lightblue = `NAME "#add8e6"
let color_peru      = `NAME "#cd853f"
let color_black     = `NAME "#000000"
let color_orange    = `NAME "#ffa500"
let color_red       = `NAME "#ff0000"
let color_green     = `NAME "#00ff00"
let color_yellow    = `NAME "#ffff00"
let color_dimgray   = `NAME "#696969"

let tractor_scale = 10
let pi = 4.0 *. atan 1.0

let printf = Printf.printf

class light ~x ~y ~name ~color ~context =
  let width, height = 20, 20 in
  let name_layout = Pango.Layout.create context in
  let _ = Pango.Layout.set_text name_layout name in
  let lwidth, lheight = Pango.Layout.get_pixel_size name_layout in
  object (self)
    (* {{{1 *)

    val mutable on = false

    method set s = on <- s

    method draw (d : GDraw.drawable) =
      let draw_circle filled =
        d#arc ~x:(x - width / 2) ~y:(y - height / 2)
              ~width:width ~height:height
              ~filled:filled ~start:0.0 ~angle:360.0 () in
      d#set_foreground (if on then color else color_dimgray);
      draw_circle true;
      d#set_foreground color_black;
      draw_circle false;
      d#put_layout ~x:(x - lwidth / 2) ~y:(y + height/2 + lheight/3)
                   ~fore:color_black name_layout

    (* }}}1 *)
  end

let rotate (pivot_x, pivot_y) angle (point_x, point_y) =
  let x' = float(point_x - pivot_x)
  and y' = float(point_y - pivot_y)
  in
  let xr = truncate (x' *. cos(angle) -. y' *. sin(angle))
  and yr = truncate (x' *. sin(angle) +. y' *. cos(angle))
  in
  (xr + pivot_x, yr + pivot_y)

let pointdiff (x1, y1) (x2, y2) = (x1 - x2, y1 - y2)
let translate (x1, y1) (x2, y2) = (x1 + x2, y1 + y2)

class component ~points ~color ?(pivot=(0,0)) () =
  object (self)
    (* {{{1 *)

    val points = points
    val color  = color
    val pivot  = pivot

    val mutable origin_x = 0
    val mutable origin_y = 0

    val mutable offset_x = 0
    val mutable offset_y = 0

    val mutable angle = 0.0

    method pivot_point = pivot

    method translate_origin ~x ~y =
      origin_x <- origin_x + x;
      origin_y <- origin_y + y

    method set_offset ~x ~y  = offset_x <- x; offset_y <- y
    method set_hor_offset ~x = offset_x <- x
    method set_ver_offset ~y = offset_y <- y
    method set_angle ~rads   = angle <- rads

    method transform point =
      let x', y' = rotate pivot angle point in
      (x' + offset_x) / tractor_scale + origin_x,
      (y' + offset_y) / tractor_scale + origin_y

    method draw (d : GDraw.drawable) =
      d#set_foreground color;
      d#polygon ~filled:true (List.map self#transform points)

    (* }}}1 *)
  end

class tractor ~context =
  (* {{{1 *)
  let loaderbucket = new component ()
      ~points:[(1228, 4204); (992, 3826); (755, 4204)]
      ~color:color_black in

  let loaderarm = new component ()
      ~points:[(1228, 4204); (1748, 3685); (1937, 3685); (2031, 3543);
               (2362, 3401); (2362, 3354); (1700, 3543); (1181, 4110)]
      ~color:color_orange in

  let frontshell = new component ()
      ~points:[(2456, 3307); (1653, 3543); (1653, 3732); (1889, 3742);
               (1889, 3826); (2362, 3779); (2362, 3921); (2456, 3921);
               (2456, 3826); (2740, 3826); (2692, 3779); (2456, 3779);
               (2456, 3732); (2409, 3685); (2409, 3590); (2456, 3307)]
      ~color:color_yellow in

  let backshell = new component ()
      ~points:[(2740, 3826); (2787, 3685); (2881, 3543); (2976, 3496);
               (3448, 3543); (3448, 3496); (3354, 3401); (2929, 3401);
               (2787, 3543); (2692, 3779); (2740, 3826)]
      ~color:color_yellow in

  let underbelly = new component ()
      ~points:[(1653, 3732); (1653, 3921); (2362, 3921); (2409, 3968);
               (2503, 3968); (2503, 4015); (2692, 4015); (2929, 3685);
               (3448, 3685); (3448, 3496); (3354, 3401); (2929, 3401);
               (2787, 3543); (2692, 3779); (2645, 3779)]
      ~color:color_dimgray in

  let cabinstruts = new component ()
      ~points:[(2409, 3307); (2598, 2692); (3401, 2692); (3401, 3501);
               (3307, 3401); (3307, 2740); (2645, 2740); (2456, 3307)]
      ~color:color_black in

  let cabinroof = new component ()
      ~points:[(2503, 2740); (2503, 2692); (2598, 2645); (2929, 2598);
               (3637, 2645); (3637, 2740); (2503, 2740)]
      ~color:color_yellow in

  let cabininterior = new component ()
      ~points:[(2456, 3307); (2551, 3259); (2692, 3401); (2692, 3496);
               (2598, 3590); (2645, 3779); (2456, 3779); (2456, 3732);
               (2409, 3685); (2409, 3590); (2456, 3307)]
      ~color:color_black in

  let cabinsteer1 = new component ()
      ~points:[(2692, 3259); (2717, 3240); (2807, 3334); (2787, 3354);
               (2692, 3259)]
      ~color:color_black in

  let cabinsteer2 = new component ()
      ~points:[(2730, 3317); (2717, 3299); (2658, 3345); (2680, 3360)]
      ~color:color_black in

  let cabinseat = new component ()
      ~points:[(2834, 3496); (2881, 3307); (3212, 3307); (3259, 3401)]
      ~color:color_black in

  let bucket = new component ()
      ~points:[(4771, 3259); (4818, 3118); (4960, 3259); (4866, 3401);
               (4582, 3496); (4440, 3448); (4393, 3307); (4299, 2976);
               (4629, 3259); (4771, 3259)]
      ~color:color_black
      ~pivot:(4900, 3300) in

  let stick = new component ()
      ~points:[(4157, 2314); (4724, 3118); (4913, 3354); (5007, 3212);
               (4913, 3070); (4818, 3070); (4535, 2598); (4582, 2456);
               (4299, 2125); (4110, 2220); (4157, 2314)]
      ~color:color_orange
      ~pivot:(4270, 2314) in

  let boom = new component ()
      ~points:[(4015, 3921); (4110, 3921); (4204, 3732); (4157, 2881);
               (4393, 2173); (4251, 2173); (4157, 2409); (3874, 2787);
               (3732, 2787); (3685, 2881); (3732, 3023); (3826, 3118);
               (4015, 3637); (4015, 3921)]
      ~color:color_yellow
      ~pivot:(4015, 3821) in

  let mount = new component ()
      ~points:[(3543, 4015); (3685, 4062); (4062, 3968); (4062, 3732);
               (3874, 3637); (3637, 3354); (3448, 3543); (3448, 3968);
               (3543, 4015)]
      ~color:color_dimgray in

  let stickpiston = new component ()
      ~points:[(4015, 2503); (4204, 2220)]
      ~color:color_black in

  let bucketpiston = new component ()
      ~points:[(4535, 2503); (4866, 3070)]
      ~color:color_black in

  (*
  let boomrod = new component ()
      ~points:[(4015, 3637); (3874, 3543); (3732, 3023); (3826, 3118);
               (4015, 3637)]
      ~color:color_orange in

  let stickrod = new component ()
      ~points:[(3732, 2787); (3968, 2503); (4062, 2503); (3874, 2787);
               (3732, 2787)]
      ~color:color_orange in
  *)

  let legs = new component ()
      ~points:[(3637, 4062); (3637, 3543); (3779, 3590); (3779, 4062);
               (3637, 4062)]
      ~color:color_red in

  (* }}}1 *)
  object
    (* {{{1 *)
    val mutable xoff = 0
    val mutable yoff = 0

    val mutable stop_pressed = false
    val mutable extend_pressed = false
    val mutable retract_pressed = false

    val components =
      [underbelly; frontshell;loaderbucket; loaderarm; backshell; cabinstruts;
       cabinroof; cabininterior; cabinsteer1; cabinsteer2; cabinseat; bucket;
       stick; boom; mount; stickpiston; bucketpiston; legs]

    val light_alarm     = new light ~x:45 ~y:120 ~name:"Alarm"
                                    ~color:color_red ~context:context
    val light_done      = new light ~x:45 ~y:170 ~name:"Done"
                                    ~color:color_green ~context:context
    val light_cancelled = new light ~x:45 ~y:220 ~name:"Cancelled"
                                    ~color:color_green ~context:context

    method shift ~x ~y =
      let shift_component c = c#translate_origin ~x:x ~y:y in
      List.iter shift_component components;
      xoff <- x;
      yoff <- y

    method draw (d : GDraw.drawable) =
      let draw_component c = c#draw d in
      let draw_circle diameter (x, y) =
        d#arc ~x:((x / tractor_scale) + xoff)
              ~y:((y / tractor_scale) + yoff)
              ~width:(diameter/tractor_scale)
              ~height:(diameter/tractor_scale)
              ~filled:true ~start:0.0 ~angle:360.0 ()
      in
      List.iter draw_component components;

      d#set_foreground color_black;
      draw_circle 672 (2876, 3585); (* rear tyre *)
      draw_circle 472 (1748, 3780); (* front tyre *)
      d#set_foreground color_yellow;
      draw_circle 352 (3036, 3745); (* rear wheel *)
      draw_circle 222 (1873, 3910); (* front wheel *)

      (* lights *)
      light_alarm#draw d;
      light_done#draw d;
      light_cancelled#draw d

    method but_stop ()    = stop_pressed <- true
    method but_retract () = retract_pressed <- true
    method but_extend ()  = extend_pressed <- true

    method update leg_pos boom_angle stick_angle bucket_angle
                  alarm_lamp done_lamp cancel_lamp =
      begin
        legs#set_ver_offset (truncate(leg_pos) * tractor_scale);

        boom#set_angle boom_angle;

        let stickfix = stick#pivot_point in
        let stickfix' = rotate boom#pivot_point boom_angle stickfix in
        let stick_trans = pointdiff stickfix' stickfix in
        let (stick_x, stick_y) = stick_trans in

        stick#set_angle (stick_angle +. boom_angle);
        stick#set_offset ~x:stick_x ~y:stick_y;

        let bucketfix = bucket#pivot_point in
        let bucketfix' = rotate boom#pivot_point boom_angle bucketfix in
        let bucketfix' = rotate stickfix' stick_angle bucketfix' in
        let (bucket_x, bucket_y) = pointdiff bucketfix' bucketfix in

        bucket#set_angle (bucket_angle +. stick_angle +. boom_angle);
        bucket#set_offset ~x:bucket_x ~y:bucket_y;

        light_alarm#set alarm_lamp;
        light_done#set done_lamp;
        light_cancelled#set cancel_lamp
      end

    method sample () =
      let r = (stop_pressed, retract_pressed, extend_pressed) in
      stop_pressed    <- false;
      retract_pressed <- false;
      extend_pressed  <- false;
      r

    (* }}}1 *)
  end

class window () =
  (* {{{1 *)

  let w = GWindow.window
     ~title:"Backhoe"
     ~width:canvas_width
     ~height:canvas_height
     ~resizable:false
     () in
  let pm = GDraw.pixmap
      ~width:canvas_width
      ~height:canvas_height
      () in
  let context = w#misc#create_pango_context in
  let _ = context#set_font_description (Pango.Font.from_string "Sans 9") in

  (* }}}1 *)
  object (self)
    (* {{{1 *)

    val window = w
    val pixmap = pm
    val tractor = new tractor ~context:context#as_context

    method draw =
      let d = (pixmap :> GDraw.drawable) in
      let (mx, my) = d#size in

      (* draw sky *)
      d#set_foreground color_lightblue;
      d#rectangle ~x:0 ~y:0 ~filled:true ~width:mx ~height:my ();

      (* draw ground *)
      d#set_foreground color_peru;
      d#rectangle ~x:0 ~y:375 ~filled:true ~width:mx ~height:my ();

      (* draw the tractor *)
      tractor#draw d;

      window#misc#draw None

    method destroy () =
      GMain.Main.quit ()

    method show =
      window#show ();
      self#draw

    method tractor = tractor

    initializer
      ignore (window#connect#destroy   ~callback:self#destroy);

      let fixed = GPack.fixed
          ~width:canvas_width
          ~height:canvas_height
          ~packing:w#add
          () in

      (* add canvas *)
      let _ = GMisc.pixmap
          pixmap
          ~width:canvas_width
          ~height:canvas_height
          ~packing:(fixed#put ~x:0 ~y:0)
          () in

      (* create operator buttons *)
      let operator_box = GPack.vbox
        ~width:100
        ~packing:(fixed#put ~x:0 ~y:0) () in
      let b_stop = GButton.button
        ~label:"stop"
        ~packing:operator_box#pack
        () in
      let b_extend = GButton.button
        ~label:"extend"
        ~packing:operator_box#pack
        () in
      let b_retract = GButton.button
        ~label:"retract"
        ~packing:operator_box#pack
        () in
      ignore (b_stop#connect#clicked    ~callback:tractor#but_stop);
      ignore (b_extend#connect#clicked  ~callback:tractor#but_extend);
      ignore (b_retract#connect#clicked ~callback:tractor#but_retract);

      tractor#shift ~x:(-60) ~y:(-50)

      (* }}}1 *)
  end

type backhoe = window * tractor

let leg_range    = (0.0, 25.0, 0.0)
let boom_range   = (0.0, 5.1 *. pi /. 10.0, 0.0)
let stick_range  = (-2.0 *. pi /. 3.0, -0.05, -.0.05)
let bucket_range = (-. 2.0 *. pi /. 3.0, 0.0, 0.0)

let show () =
  let w = new window () in
  let _ = w#show in
  w, w#tractor

let update (window, tractor)
           leg_pos boom_angle stick_angle bucket_angle
           alarm_lamp done_lamp cancel_lamp =
  begin
    tractor#update leg_pos boom_angle stick_angle bucket_angle
                   alarm_lamp done_lamp cancel_lamp;
    window#draw
  end

let sample (_, tractor) =tractor#sample ()

(* Work around a problem in the compilation of fby TPB:20110319 *)
let state = ref (None : backhoe option)
let showupdate (leg_pos, boom_angle, stick_angle, bucket_angle,
               alarm_lamp, done_lamp, cancel_lamp) =
  let st =
    match !state with
    | None -> let st = show () in
              (state := Some st; st)
    | Some s -> s in
  update st leg_pos boom_angle stick_angle bucket_angle
            alarm_lamp done_lamp cancel_lamp

let showsample () =
    match !state with
    | None -> (false, false, false)
    | Some s -> sample s

(* test harness *)
let runtest () =
  let tractor = show () in
  update tractor 25.0 0.0 (-. pi *. 0.666) (1.4 *. pi) true false true;
  GMain.Main.main ()
