
type signal_type =
  | Points of bool
  | PiecewiseContinuous of bool
  | LinearInterpolation

let points x  = Points x
let piecewise   = PiecewiseContinuous false
let square      = PiecewiseContinuous true
let linear      = LinearInterpolation

let len_history = ref 5000

let scope_title_height  = 30
let scope_title_height  = 30
let y_axis_width        = 80
let x_axis_height       = 20

let scope_padding_right = 30
let scope_offset_top    = 5
let scope_offset_bottom = 5

let min_scope_height    = 120
let max_scope_height    = 1000
let min_scope_width     = 200 + y_axis_width + scope_padding_right
let max_scope_width     = 2500

let gridline_color = `NAME "#f2f2f2"

let sig_colors =
  [|`NAME "red";
    `NAME "blue";
    `NAME "green";
    `NAME "orange";
    `NAME "brown";
    `NAME "magenta";
    `NAME "cyan";
  |]
let num_sig_colors = Array.length sig_colors

let round x = int_of_float (floor (x +. 0.5))
let nearest_powten x = 10.0 ** (floor (log10 x +. 0.5));;

let float_to_string x =
  let t = int_of_float (log10 x) in
  if -4 <= t && t <= 3
  then Printf.sprintf "%f" x
  else Printf.sprintf "%e" x

let fill_drawable (d : GDraw.drawable) color =
  let (mx, my) = d#size in
  d#set_foreground color;
  d#rectangle ~x:0 ~y:0 ~filled:true ~width:mx ~height:my ()

let icon_zoom_out_hor =
  let icon_zoom_out_hor_data = [|
      "16 16 7 1";
      "   c None";
      ".  c #000000";
      "+  c #505050";
      "@  c #8F8F8F";
      "#  c #FFFFFF";
      "$  c #3E3E3E";
      "%  c #6F6F6F";
      "                ";
      "                ";
      "                ";
      "                ";
      "   ..........   ";
      "   .+@@@@@@+.   ";
      " . .@######@. . ";
      "....$%####%$....";
      "....$%####%$....";
      " . .@######@. . ";
      "   .+@@@@@@+.   ";
      "   ..........   ";
      "                ";
      "                ";
      "                ";
      "                ";
    |]
  in
  GdkPixbuf.from_xpm_data icon_zoom_out_hor_data

let icon_zoom_out_ver =
  let icon_zoom_out_ver_data = [|
      "16 16 6 1";
      "   c None";
      ".  c #000000";
      "+  c #505050";
      "@  c #8F8F8F";
      "#  c #3E3E3E";
      "$  c #FFFFFF";
      "       ..       ";
      "      ....      ";
      "       ..       ";
      "       ..       ";
      "   ..........   ";
      "   .+@@##@@+.   ";
      "   .@$$$$$$@.   ";
      "   .@$$$$$$@.   ";
      "   .@$$$$$$@.   ";
      "   .@$$$$$$@.   ";
      "   .+@@##@@+.   ";
      "   ..........   ";
      "       ..       ";
      "       ..       ";
      "      ....      ";
      "       ..       ";
    |]
  in
  GdkPixbuf.from_xpm_data icon_zoom_out_ver_data

let icon_zoom_out =
  let icon_zoom_out_data = [|
      "16 16 7 1";
      "   c None";
      ".  c #000000";
      "+  c #505050";
      "@  c #8F8F8F";
      "#  c #3E3E3E";
      "$  c #FFFFFF";
      "%  c #6F6F6F";
      "       ..       ";
      "      ....      ";
      "       ..       ";
      "       ..       ";
      "   ..........   ";
      "   .+@@##@@+.   ";
      " . .@$$$$$$@. . ";
      "....#%$$$$%#....";
      "....#%$$$$%#....";
      " . .@$$$$$$@. . ";
      "   .+@@##@@+.   ";
      "   ..........   ";
      "       ..       ";
      "       ..       ";
      "      ....      ";
      "       ..       ";
    |]
  in
  GdkPixbuf.from_xpm_data icon_zoom_out_data

let icon_zoom_in =
  let icon_zoom_in_data = [|
      "16 16 5 1";
      "   c None";
      ".  c #000000";
      "+  c #505050";
      "@  c #8F8F8F";
      "#  c #FFFFFF";
      "                ";
      "                ";
      "                ";
      "                ";
      "   ..........   ";
      "   .+@@@@@@+.   ";
      "   .@######@.   ";
      "   .@######@.   ";
      "   .@######@.   ";
      "   .@######@.   ";
      "   .+@@@@@@+.   ";
      "   ..........   ";
      "                ";
      "                ";
      "                ";
      "                ";
    |]
  in
  GdkPixbuf.from_xpm_data icon_zoom_in_data

class signal (n : string) (t : signal_type) =
  object
    val name = n
    val ty   = t

    val data = Array.make !len_history 0.0
    val mutable newval = 0.0

    method name = name

    method sample v = newval <- v
    method tick i   = data.(i) <- newval

    method data i = data.(i)

    method draw_sample (d : GDraw.drawable) pyv last (xt, yi) =
      let y = pyv data.(yi) in
      match ty with
      | Points with_step -> begin
            d#arc ~x:(xt - 2) ~y:(y - 2)
                  ~width:4 ~height:4
                  ~filled:true ();
            if with_step then d#lines [(xt, max_int / 10); (xt, y)]
          end

      | PiecewiseContinuous false -> begin
            d#arc ~x:(xt - 2) ~y:(y - 2)
                  ~width:4 ~height:4
                  ~filled:true ();
             match last with
             | None -> ()
             | Some (lxt, lyi) ->
                 let ly = pyv data.(lyi) in
                 d#line lxt ly xt ly
          end

      | PiecewiseContinuous true -> begin
             match last with
             | None ->
                d#arc ~x:(xt - 1) ~y:(y - 1)
                      ~width:2 ~height:2
                      ~filled:true ();
             | Some (lxt, lyi) ->
                 let ly = pyv data.(lyi) in
                 d#line lxt ly xt ly;
                 d#line xt ly xt y
          end

      | LinearInterpolation -> begin
             match last with
             | None ->
                 d#arc ~x:(xt - 1) ~y:(y - 1)
                       ~width:2 ~height:2
                       ~filled:true ();

             | Some (lxt, lyi) ->
                 let ly = pyv data.(lyi) in
                 d#line lxt ly xt y
          end
  end

class image_selection_box
    ?height ?width ?xalign ?yalign ?border_width ?packing ?callback
    ?(fill_horizontally = false) ?(fill_vertically = false)
    ?(x_offset = 0) ?(y_offset = 0)
    ()
  =
  let ebox = GBin.event_box ?border_width:border_width ?packing:packing () in
  let img = GMisc.image
      ?height:height
      ?width:width
      ~packing:ebox#add
      ?xalign:xalign
      ?yalign:yalign
      () in

  let make_rect (x, y, x', y') =
    let x, y = min x x', min y y'
    and w, h = abs (x - x'), abs (y - y')
    in (x, y, w, h) in

  let no_last_coords = (0, 0, 0, 0) in

  object (self)
    val evbox = ebox
    val image = img
    val zoom_in_callback = callback

    val mutable xi = 0
    val mutable yi = 0

    val mutable last_coords = no_last_coords

    val mutable width  = 0
    val mutable height = 0

    val fill_hor = fill_horizontally
    val fill_ver = fill_vertically

    method image = image

    method redraw () =
      if (last_coords <> no_last_coords) then self#draw last_coords

    method private draw coords =
      let (x, y, w, h) = make_rect coords in
      let d = (image#pixmap :> GDraw.drawable) in
      Gdk.GC.set_function d#gc `INVERT;
      d#rectangle ~x:x ~y:y ~width:w ~height:h ~filled:true ();
      last_coords <- coords

    method private undraw =
      if last_coords <> no_last_coords then
        (self#draw last_coords; last_coords <- no_last_coords)

    method private button_down ev =
      if GdkEvent.Button.button ev <> 1 then false
      else begin
        let w, h = Gdk.Drawable.get_size image#misc#window in
        width <- w;
        height <- h;
        xi <- if fill_horizontally then 0
              else int_of_float (GdkEvent.Button.x ev);
        yi <- if fill_vertically then 0
              else int_of_float (GdkEvent.Button.y ev);
        true
      end

    method private button_up ev =
      if GdkEvent.Button.button ev <> 1
         || last_coords = no_last_coords then false
      else begin
        let (x, y, x', y') = last_coords in
        self#undraw;
        image#misc#draw None;
        match zoom_in_callback with
        | Some f ->
            let hor_range =
              if fill_hor then None
              else Some (max 0 ((min x x') - x_offset),
                         max 0 ((max x x') - x_offset))
            and ver_range =
              if fill_ver then None
              else Some (max 0 ((min y y') - y_offset),
                         max 0 ((max y y') - y_offset))
            in f hor_range ver_range; true

        | None -> true
      end

    method private hold_drag ev =
      let x = if fill_horizontally then width
              else int_of_float (GdkEvent.Motion.x ev)
      and y = if fill_vertically then height
              else int_of_float (GdkEvent.Motion.y ev)
      in
      let new_coords = (xi, yi, x, y) in
      self#undraw;
      self#draw new_coords;
      image#misc#draw None;
      true

    initializer
      ignore (evbox#event#connect#button_release ~callback:self#button_up);
      ignore (evbox#event#connect#button_press   ~callback:self#button_down);
      ignore (evbox#event#connect#motion_notify  ~callback:self#hold_drag);
      evbox#event#add [`BUTTON1_MOTION]
  end

class scope (yl : float) (yu : float) (sigs : signal list) =
  object (self)

    val mutable min_y = yl
    val mutable max_y = yu

    val mutable title = ""

    method title = title

    method set_yrange (yl, yu) = (min_y <- yl; max_y <- yu)

    val signals =
      let add_color (n, l) s =
        ((n + 1) mod num_sig_colors, (sig_colors.(n), s)::l)
      in
      snd (List.fold_left add_color (0, []) sigs)

    val mutable scope_image = GMisc.image ()
    val mutable yaxis_image = GMisc.image ()

    val mutable redraw_zoomin  = (fun () -> ())
    val mutable zoom_in_hor    = (fun _ -> ())

    val mutable bgcolor = `WHITE

    method set_bgcolor c = bgcolor <- c

    method title_from_signals =
      let add_markup (color, signal) =
        let cname =
          match color with
          | `NAME n -> n
          | `BLACK  -> "black"
          | `WHITE  -> "white"
          | `RGB (r, g, b) -> Printf.sprintf "#%02x%02x%02x" r g b
          | `COLOR _ -> "black"
        in
        Printf.sprintf "<span foreground=\"%s\">%s</span>" cname signal#name
      in
      title <- String.concat ", " (List.map add_markup (List.rev signals))

    method bind_to_window win_pack =
      let scopebox = GPack.hbox ~packing:win_pack () in

      let yaxis = new image_selection_box
        ~callback:self#zoom_in
        ~border_width:0
        ~xalign:0.0
        ~yalign:1.0
        ~packing:(scopebox#pack ~expand:false)
        ~fill_horizontally:true
        ()
      in

      let selbox = new image_selection_box
        ~callback:self#zoom_in
        ~border_width:0
        ~xalign:0.0
        ~yalign:1.0
        ~packing:(scopebox#pack ~expand:false)
        ()
      in
      yaxis_image   <- yaxis#image;
      scope_image   <- selbox#image;
      redraw_zoomin <- (fun () -> (selbox#redraw (); yaxis#redraw ()));
      self#zoom_in

    method set_zoom_in_hor f = zoom_in_hor <- f

    method adjust w h =
      let nh = h
      and nw = w - y_axis_width - scope_padding_right + 1
      in

      let reallocate =
        try
          let ow, oh = scope_image#pixmap#size in
          ow <> nw || oh <> nh
        with Gpointer.Null -> true
      in

      if reallocate then begin
        let scope_pixmap = GDraw.pixmap ~width:nw ~height:nh () in
        scope_image#set_pixmap scope_pixmap;

        let yaxis_pixmap = GDraw.pixmap ~width:y_axis_width ~height:nh () in
        yaxis_image#set_pixmap yaxis_pixmap
      end;

      reallocate

    method clear =
      let pixmap = (scope_image#pixmap :> GDraw.drawable) in
      fill_drawable pixmap `WHITE;

    method draw_x_gridline x =
      let pixmap = (scope_image#pixmap :> GDraw.drawable) in
      let w, h = pixmap#size in
      pixmap#set_foreground gridline_color;
      pixmap#line x 0 x h

    method draw_y_gridline y =
      let pixmap = (scope_image#pixmap :> GDraw.drawable) in
      let w, h = pixmap#size in
      pixmap#set_foreground gridline_color;
      pixmap#line 0 y w y

    method private get_pixel_of_value h =
      let axis_height = h - scope_offset_top - scope_offset_bottom in
      let pyv =
        let pixels_per_v = float axis_height /. (max_y -. min_y) in
        fun v ->
          min 32767 (max (-32767) ( (* limit pixels to avoid "wraparound" *)
          (h - scope_offset_bottom
             - int_of_float (pixels_per_v *. (v -. min_y)))))
      in
      (axis_height, pyv)

    method private get_value_of_pixel h =
      let axis_height = h - scope_offset_top - scope_offset_bottom in
      let v_per_pixel = (max_y -. min_y) /. float axis_height
      and my = min_y in
      fun p -> (float (h - p) *. v_per_pixel) +. my

    method private zoom_in hor_range ver_range =
      let pixmap = (yaxis_image#pixmap :> GDraw.drawable) in
      let _, h = pixmap#size in
      let ptov = self#get_value_of_pixel h in
      (match ver_range with
       | None -> ()
       | Some (yu, yl) -> (min_y <- max min_y (ptov yl);
                           max_y <- min max_y (ptov yu)));
      zoom_in_hor hor_range

    method draw_y_axis context =
      let pixmap = (yaxis_image#pixmap :> GDraw.drawable) in
      let w, h = pixmap#size in
      let axis_height, pyv = self#get_pixel_of_value h in
      let tick_l, tick_r = w - 7, w - 1 in

      fill_drawable pixmap bgcolor;
      pixmap#set_foreground `BLACK;
      pixmap#line tick_r 0 tick_r h;

      (* by default, two markers every 100 pixels, with at least 2
         and prefer 'clean' powers of ten *)
      let dninc = (max 1 (axis_height / 100)) * 8 in
      let vinc = nearest_powten ((max_y -. min_y) /. float dninc) in
      let ninc = int_of_float ((max_y -. min_y) /. vinc) in

      let layout = Pango.Layout.create context in
      Pango.Layout.set_text layout "0E";
      let _, lheight = Pango.Layout.get_pixel_size layout in
      let npossible = max 1 (axis_height / (lheight + 6) + 1) in
      let skipinc = if npossible >= ninc then 1 else ninc / npossible in

      for i = 0 to ninc do
        if i mod skipinc = 0 then begin
          let v = min_y +. (float i *. vinc) in
          let y = pyv v in

          pixmap#lines [(tick_l,y); (tick_r,y)];
          self#draw_y_gridline y;

          Pango.Layout.set_text layout (float_to_string v);
          let lwidth, _ = Pango.Layout.get_pixel_size layout in
          pixmap#put_layout
            ~x:(tick_r - lwidth - 8)
            ~y:(y - lheight/2 + 1)
            ~fore:`BLACK layout
        end
      done

    method draw (indices : unit -> (int * int) option) =
      let pixmap = (scope_image#pixmap :> GDraw.drawable) in
      let _, h = pixmap#size in
      let _, pyv = self#get_pixel_of_value h in

      let prev = ref None in
      let rec iter () =
        match indices () with
        | None -> ()
        | Some curr -> begin
              let draw_sig (c, s) =
                pixmap#set_foreground c;
                s#draw_sample pixmap pyv !prev curr
              in
              List.iter draw_sig signals;
              prev := Some curr;
              iter ()
            end
      in
      iter ();
      redraw_zoomin ()

    method private get_min_max (indices : unit -> (int * int) option) =
      let rec iter (lv, uv) =
        match indices () with
        | None -> (lv, uv)
        | Some (_, i) ->
            let nlv = List.fold_left (fun l s -> min l (s#data i)) lv sigs
            and nuv = List.fold_left (fun h s -> max h (s#data i)) uv sigs
            in
            iter (nlv, nuv)
      in
      iter (max_float, min_float)

    method zoom_out_ver indices =
      let lv, uv = self#get_min_max indices in

      if (lv < min_y) || (uv > max_y)
      then (min_y <- lv; max_y <- uv; true)
      else let delta = (max_y -. min_y) *. 0.2 in
           (min_y <- min_y -. delta;
            max_y <- max_y +. delta;
            false)

    method zoom_fit indices =
      let lv, uv = self#get_min_max indices in
      min_y <- lv;
      max_y <- uv

    method tick i =
      List.iter (fun (_, s) -> s#tick i) signals

    initializer
      self#title_from_signals

  end

class window title initial_max_t (scs : scope list) =
  let screen = Gdk.Screen.default () in
  let w = truncate (float (Gdk.Screen.width  ~screen:screen ()) *. 0.8) in
  let h = truncate (float (Gdk.Screen.height ~screen:screen ()) *. 0.8) in

  let w    = GWindow.window ~title:title ~height:h ~width:w () in
  let wbox = GPack.vbox ~packing:w#add ()  in
  let xaxis_context = w#misc#create_pango_context in
  let fontdesc = Pango.Font.from_string "Sans 7" in
  let _ = xaxis_context#set_font_description fontdesc in

  let default_cursor = Gdk.Cursor.create `CROSSHAIR in

  (* Add two or three rows for each scope:
       title (optional), scope box, xaxis image *)
  let make_scope scope =
    ignore (GMisc.label ~markup:scope#title ~height:scope_title_height
                        ~packing:(wbox#pack) ());
    let sbox = GPack.hbox ~packing:wbox#pack () in
    let zoom_in_fn = scope#bind_to_window (fun w -> sbox#pack w) in
    let butbox = GPack.vbox ~packing:sbox#pack () in

    let xaxis = new image_selection_box
      ~callback:zoom_in_fn
      ~height:x_axis_height
      ~x_offset:y_axis_width
      ~border_width:0
      ~xalign:0.0
      ~yalign:0.0
      ~packing:wbox#pack
      ~fill_vertically:true
      ()
    in

    (scope, xaxis, (fun b -> butbox#pack b))
  in

  object (self)
    val mutable min_t = 0.0
    val mutable max_t = initial_max_t

    val time = Array.make !len_history 0.0

    val mutable curr_idx = 0
    val mutable nsamples = 0

    val window  = w
    val context = xaxis_context#as_context

    val mutable bgcolor = `WHITE

    val mutable scopes = List.map make_scope scs;

    method private iter_scopes f =
      List.iter (fun (s, _, _) -> f s) scopes

    method private destroy () = GMain.Main.quit ()

    method private sample_idx i =
      (* first sample = 0, nsamples, 2 * nsamples, ...
         last  sample = -1, nsamples - 1, ... *)
      let i = (if i < 0 then nsamples else 0) + i mod nsamples in
      let time_len = Array.length time in
      let base = if nsamples < time_len then 0 else curr_idx in
      (base + i) mod time_len

    method private time i = time.(self#sample_idx i)

    method tick t =
      let time_len = Array.length time in

      time.(curr_idx) <- t;
      self#iter_scopes (fun s -> s#tick curr_idx);

      curr_idx <- (curr_idx + 1) mod time_len;
      nsamples <- min (nsamples + 1) time_len;

      let prev_idx = if nsamples = 1 then 0 else nsamples - 2 in

      let t_delta = t -. self#time prev_idx in

      if (t_delta > 0.0 && t > max_t) then begin
        max_t <- max_t +. t_delta;
        min_t <- min_t +. t_delta
      end

    method private get_x_axis =
      let _, selbox, _ = List.hd scopes in
      let pixmap = (selbox#image#pixmap :> GDraw.drawable) in
      let w, _ = pixmap#size in
      let axis_width = w - y_axis_width - scope_padding_right in

      let pixels_per_t = float axis_width /. (max_t -. min_t) in
      let pxt =
        fun t -> int_of_float (pixels_per_t *. (t -. min_t))
      in
      pixmap, axis_width, pxt

    method private get_time_of_pixel =
      let _, selbox, _ = List.hd scopes in
      let pixmap = (selbox#image#pixmap :> GDraw.drawable) in
      let w, _ = pixmap#size in
      let axis_width = w - y_axis_width - scope_padding_right in
      let t_per_pixels = (max_t -. min_t) /. float axis_width
      and mt = min_t in
      fun p -> (float_of_int p *. t_per_pixels) +. mt

    method private zoom_in_hor hor_range =
      let ptot = self#get_time_of_pixel in
      (match hor_range with
       | None -> ()
       | Some (xl, xu) -> (min_t <- max min_t (ptot xl);
                           max_t <- min max_t (ptot xu)));
      self#draw

    method adjust =
      let _, selbox, _ = List.hd scopes in
      let w, h = Gdk.Drawable.get_size window#misc#window in
      let nw = min max_scope_width (max min_scope_width w) in

      let pw =
        try
          let pixmap = (selbox#image#pixmap :> GDraw.drawable) in
          fst (pixmap#size)
        with Gpointer.Null -> -1
      in

      if nw <> pw then begin
        let pixmap = GDraw.pixmap ~width:nw ~height:x_axis_height () in
        List.iter (fun (_, selbox, _) -> selbox#image#set_pixmap pixmap) scopes
      end;

      let nsc = List.length scopes in
      let sch = min max_scope_height (max min_scope_height
                  ((h / nsc) - x_axis_height - scope_title_height))
      and scw = min max_scope_width (max min_scope_width w)
      in
      let adjust_scope changed (sc, _, _) = sc#adjust scw sch || changed in
      if List.fold_left adjust_scope (nw <> pw) scopes then self#draw

    method private draw_x_axis =
      let pixmap, axis_width, pxt = self#get_x_axis in
      fill_drawable pixmap bgcolor;
      pixmap#set_foreground `BLACK;
      pixmap#line (y_axis_width - 1) 0 (axis_width + y_axis_width) 0;

      self#iter_scopes (fun s -> s#clear);

      (* by default, two markers every 100 pixels, but insist on having
         at least 10 and prefer 'clean' powers of ten *)
      let dninc = (max 5 (axis_width / 100)) * 2 in
      let tinc = nearest_powten ((max_t -. min_t) /. float dninc) in
      let ninc = int_of_float ((max_t -. min_t) /. tinc) in

      (* calculate the number of labels possible for the given width *)
      let layout = Pango.Layout.create context in
      Pango.Layout.set_text layout (float_to_string (min_t +. tinc));
      let lwidth, _ = Pango.Layout.get_pixel_size layout in
      let npossible = max 1 (axis_width / (lwidth * 2 + 15) + 1) in
      let skipinc = if npossible >= ninc then 1 else ninc / npossible in

      (* draw the markers and labels *)
      for i = 0 to ninc do
        if i mod skipinc = 0 then begin
          let t = min_t +. (float i *. tinc) in
          let x = pxt t + y_axis_width in

          pixmap#lines [(x,0); (x,8)];
          self#iter_scopes (fun s -> s#draw_x_gridline (x - y_axis_width));

          Pango.Layout.set_text layout (float_to_string t);
          let lwidth, _ = Pango.Layout.get_pixel_size layout in
          pixmap#put_layout
            ~x:(x - 2 - lwidth / 2)
            ~y:9
            ~fore:`BLACK layout
        end
      done

    method private fold_samples f acc =
      if nsamples = 0 then acc
      else
        let a = ref acc in
        for i = 0 to nsamples - 1 do
          a := f !a (self#time i)
        done;
        !a

    method private get_iterator =
      let _, _, pxt = self#get_x_axis in
      let iterator all =
        if nsamples = 0 then (fun () -> None)
        else
          let idx = ref 0 in
          let lasti_gtmax i = i <> 0 && self#time (i - 1) > max_t in

          let rec next () =
            let i = !idx in
            incr idx;
            if i = nsamples || (not all && self#time i > max_t && lasti_gtmax i)
            then None
            else if (not all && self#time i < min_t && self#time (i + 1) < min_t)
            then next ()
            else
              let sample_i = self#sample_idx i in
              Some (pxt (time.(sample_i)), sample_i)
          in next

      in iterator

    method draw =
      self#draw_x_axis;
      List.iter (fun (_, selbox, _) -> selbox#redraw ()) scopes;
      let sample_points = self#get_iterator in
      self#iter_scopes (fun s -> s#draw_y_axis context;
                                 s#draw (sample_points false));
      w#misc#draw None

    method private zoom_out_hor fit_to_scope_only =
      let f (low_t, high_t) t = (min low_t t, max high_t t) in
      let low_t, high_t = self#fold_samples f (max_float, min_float) in

      if nsamples > 0 then begin
        min_t <- low_t;

        if (max_t >= high_t && not fit_to_scope_only)
        then max_t <- max_t +. 0.5 *. (max_t -. min_t)
        else max_t <- high_t
      end;
      self#draw

    method private zoom_fit =
      if nsamples > 0 then begin
        min_t <- self#time 0;
        max_t <- self#time (nsamples - 1)
      end;
      self#draw

    method private add_buttons (scope, _, pack_button) =
      let add_button icon callback =
        let image = GMisc.image ~pixbuf:icon () in
        let button = GButton.button ~packing:pack_button () in
        ignore (button#set_image (image :> GObj.widget));
        ignore (button#connect#clicked ~callback:callback) in

      let zoom_out_ver () =
        (ignore (scope#zoom_out_ver (self#get_iterator true)); self#draw)
      and zoom_out_hor () =
        self#zoom_out_hor false in

      let zoom_out_all () =
        (self#zoom_out_hor (scope#zoom_out_ver (self#get_iterator true));
         self#draw) in

      let zoom_fit () =
        (scope#zoom_fit (self#get_iterator true); self#zoom_fit)
      in

      add_button icon_zoom_out_hor zoom_out_hor;
      add_button icon_zoom_out zoom_out_all;
      add_button icon_zoom_out_ver zoom_out_ver;
      add_button icon_zoom_in zoom_fit

    method private show () =
      bgcolor <- `COLOR (window#misc#style#bg `NORMAL);
      self#iter_scopes
        (fun s -> s#set_bgcolor bgcolor; s#set_zoom_in_hor self#zoom_in_hor);
      ignore (window#misc#connect#size_allocate (fun _ -> self#adjust));
      self#adjust

    initializer
      List.iter self#add_buttons scopes;
      ignore (window#connect#destroy ~callback:self#destroy);
      ignore (window#misc#connect#show ~callback:self#show);
      window#set_allow_shrink true;
      window#show ();
      Gdk.Window.set_cursor window#misc#window default_cursor

  end

let getSignals l = List.map (fun (a,b,_) -> (a,b)) l
let getValues l = List.map (fun (_,_,a) -> a) l

let signal (name, ty) = new signal name ty
let signal_l l = List.map (fun (name, ty) -> signal (name, ty)) l
let scope (yl, yu, signals)  = new scope yl yu signals
let window (imax_t, scopes, scope_list) = new window imax_t scopes scope_list

let update (s, v) = s#sample v
let update_l (ls, l) = List.iter2 (fun s v -> update (s, v)) ls l
let tick (w, t) = (w#tick t; w#draw)
