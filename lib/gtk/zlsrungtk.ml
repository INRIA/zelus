module Make (SSolver : Zls.STATE_SOLVER) =
struct (* {{{ *)

(* instantiate a numeric solver *)
module Solver = Zlsolve.Make (SSolver) (Illinois)

let _ = GMain.init () (* initialize lablgtk2 *)

let start_playing = ref true

let destroy () = GMain.Main.quit ()

let low_prio = Glib.int_of_priority `LOW
external timeout_add : ?prio:int -> ms:int -> callback:(unit -> bool)
                       -> Glib.Timeout.id
  = "ml_g_timeout_add"

class step_task main_alloc main_csize main_zsize main_horizon main_maxsize
                main_ders main_step main_zero main_reset =
object (self)

  val stepfn =
    Solver.step
      main_alloc
      main_csize
      main_zsize
      main_horizon
      main_maxsize
      main_ders
      main_step
      main_zero
      main_reset

  val mutable last_wall_clk = Unix.gettimeofday ()
  val mutable timer_id = None
  val mutable step_count = 0

  method private inc_step_count () = step_count <- step_count + 1
  method private reset_step_count () = step_count <- 0
  method private too_many_steps = step_count > 1000

  method private clear_timer () =
    match timer_id with
      None -> ()
    | Some id -> (Glib.Timeout.remove id;
                  timer_id <- None)

  method single_step () =
    let _, is_done, _ = stepfn () in
    is_done

  method trigger_step () =
    self#clear_timer ();
    self#inc_step_count ();
    let _, is_done, delta = stepfn () in
    let wall_clk = Unix.gettimeofday () in
    let delta' = delta -. (wall_clk -. last_wall_clk) in
    last_wall_clk <- wall_clk;
    if is_done then true
    else if delta <= 0.0 && not self#too_many_steps then self#trigger_step ()
    else
      (* NB: cut losses at each continuous step: *)
      if self#too_many_steps then begin
         prerr_string "Zlsrungtk: too fast!\n";
         flush stderr;
         self#reset_step_count ();
         (* Give GTK a chance to process other events *)
         timer_id <- Some (timeout_add ~prio:low_prio ~ms:10
                                       ~callback:self#trigger_step);
         true
        end
      else if delta' <= 0.0 then self#trigger_step ()
      else (
        (* NB: accumulate losses across steps: *)
        (* wall_clk_last := wall_clk; *)
        self#reset_step_count ();
        timer_id <- Some (timeout_add ~prio:low_prio
                           ~ms:(int_of_float (delta' *. 1000.0))
                           ~callback:self#trigger_step);
        true)

  method start () =
    last_wall_clk <- Unix.gettimeofday ();
    ignore (self#trigger_step ())

  method stop () = self#clear_timer ()
end

let go (Ztypes.Hsim { alloc      = main_alloc;
                      maxsize    = main_maxsize;
                      csize      = main_csize;
                      zsize      = main_zsize;
                      step       = main_step;
                      derivative = main_ders;
                      crossings  = main_zero;
                      reset      = main_reset;
                      horizon    = main_horizon; }) =
  let w = GWindow.window
    ~title:"Simulator"
    ~width:250
    ~height:70
    ~resizable:false
    () in

  let outer_box = GPack.vbox ~packing:w#add () in

  let top_box = GPack.button_box
    `HORIZONTAL
    ~packing:outer_box#pack
    ~child_width: 48
    ~child_height: 48
    ~layout:`SPREAD
    ()
  in

  let b_play = GButton.button
    ~packing:top_box#pack
    ~stock:`MEDIA_PLAY
    ()
  in
  let b_pause = GButton.button
    ~packing:top_box#pack
    ~stock:`MEDIA_PAUSE
    ()
  in
  let b_single = GButton.button
    ~packing:top_box#pack
    ~stock:`MEDIA_NEXT
    ()
  in
  b_pause#misc#set_sensitive false;

  let stask =
    new step_task main_alloc main_csize main_zsize main_horizon main_maxsize
                  main_ders main_step main_zero main_reset in

  let s_speed_adj = GData.adjustment
    ~lower:1.0
    ~upper:20.0
    ~value:3.0
    ~step_incr:0.2
    ()
  in
  let original_speedup = !Solver.speedup in
  let change_speedup x =
    let v = s_speed_adj#value in
    Solver.speedup := original_speedup
        *. (if v <= 3.0 then v /. 3.0 else (v -. 3.0) *. 4.0);
    ignore (stask#trigger_step ())
    in
  ignore (s_speed_adj#connect#value_changed change_speedup);

  let s_speed = GRange.scale
    `HORIZONTAL
    ~adjustment:s_speed_adj
    ~draw_value:false
    ~packing:outer_box#pack
    ()
  in
  ignore (s_speed); (* avoid compiler warning *)

  let step_react_fun () =
    try
      if Printexc.print stask#single_step () then begin
          b_single#misc#set_sensitive false;
          b_play#misc#set_sensitive false;
          b_pause#misc#set_sensitive false;
          ()
        end
    with _ -> (destroy ()) in

  let play_pushed () =
      b_single#misc#set_sensitive false;
      b_play#misc#set_sensitive false;
      b_pause#misc#set_sensitive true;
      stask#start ()
  in

  let pause_pushed () =
      b_single#misc#set_sensitive true;
      b_play#misc#set_sensitive true;
      b_pause#misc#set_sensitive false;
      stask#stop ()
  in

  ignore (b_play#connect#clicked ~callback:play_pushed);
  ignore (b_pause#connect#clicked ~callback:pause_pushed);
  ignore (b_single#connect#clicked ~callback:step_react_fun);

  if !start_playing then play_pushed ();

  ignore (w#connect#destroy ~callback:destroy);
  w#show ();
  GMain.Main.main ()

let check _ _ = assert false

end (* }}} *)

module MakeDiscrete () =
struct (* {{{ *)

let _ = GMain.init () (* initialize lablgtk2 *)

let start_playing = ref false

let destroy () = GMain.Main.quit ()

let low_prio = Glib.int_of_priority `LOW
external timeout_add : ?prio:int -> ms:int -> callback:(unit -> bool)
                       -> Glib.Timeout.id
  = "ml_g_timeout_add"

class step_task freq main_step =
object (self)

  val mutable period = 1.0 /. freq

  val mutable last_wall_clk = Unix.gettimeofday ()
  val mutable timer_id = None
  val mutable step_count = 0

  method set_period v = period <- v

  method private clear_timer () =
    match timer_id with
      None -> ()
    | Some id -> (Glib.Timeout.remove id;
                  timer_id <- None)

  method single_step () = main_step ()

  method trigger_step () =
    self#clear_timer ();
    let is_done = main_step () in
    let delta = 1.0 in
    let wall_clk = Unix.gettimeofday () in
    let delta' = delta -. (wall_clk -. last_wall_clk) in
    last_wall_clk <- wall_clk;
    if is_done then true
    else if delta' <= 0.0 then main_step ()
    else (
      (* NB: accumulate losses across steps: *)
      (* wall_clk_last := wall_clk; *)
      timer_id <- Some (timeout_add ~prio:low_prio
                         ~ms:(int_of_float (delta' *. period))
                         ~callback:self#trigger_step);
      true)

  method start () =
    last_wall_clk <- Unix.gettimeofday ();
    ignore (self#trigger_step ())

  method stop () = self#clear_timer ()
end

(* let go (main_alloc, main_step, main_reset) = *)
let go freq main_step =

  let w = GWindow.window
    ~title:"Simulator"
    ~width:250
    ~height:70
    ~resizable:false
    () in

  let outer_box = GPack.vbox ~packing:w#add () in

  let top_box = GPack.button_box
    `HORIZONTAL
    ~packing:outer_box#pack
    ~child_width: 48
    ~child_height: 48
    ~layout:`SPREAD
    ()
  in

  let b_play = GButton.button
    ~packing:top_box#pack
    ~stock:`MEDIA_PLAY
    ()
  in
  let b_pause = GButton.button
    ~packing:top_box#pack
    ~stock:`MEDIA_PAUSE
    ()
  in
  let b_single = GButton.button
    ~packing:top_box#pack
    ~stock:`MEDIA_NEXT
    ()
  in
  b_pause#misc#set_sensitive false;

  let stask = new step_task freq (fun () -> main_step (); false) in

  let s_speed_adj = GData.adjustment
    ~lower:1.0
    ~upper:100.0
    ~value:10.0
    ~step_incr:1.0
    ()
  in
  let change_period x =
    stask#set_period (10. /. s_speed_adj#value)
    in
  ignore (s_speed_adj#connect#value_changed change_period);

  let s_speed = GRange.scale
    `HORIZONTAL
    ~adjustment:s_speed_adj
    ~draw_value:false
    ~packing:outer_box#pack
    ()
  in
  ignore (s_speed); (* avoid compiler warning *)

  let step_react_fun () =
    try
      if Printexc.print stask#single_step () then begin
          b_single#misc#set_sensitive false;
          b_play#misc#set_sensitive false;
          b_pause#misc#set_sensitive false;
          ()
        end
    with _ -> (destroy ()) in

  let play_pushed () =
      b_single#misc#set_sensitive false;
      b_play#misc#set_sensitive false;
      b_pause#misc#set_sensitive true;
      stask#start ()
  in

  let pause_pushed () =
      b_single#misc#set_sensitive true;
      b_play#misc#set_sensitive true;
      b_pause#misc#set_sensitive false;
      stask#stop ()
  in

  ignore (b_play#connect#clicked ~callback:play_pushed);
  ignore (b_pause#connect#clicked ~callback:pause_pushed);
  ignore (b_single#connect#clicked ~callback:step_react_fun);

  if !start_playing then play_pushed () else step_react_fun ();

  ignore (w#connect#destroy ~callback:destroy);
  w#show ();
  GMain.Main.main ()

end (* }}} *)
