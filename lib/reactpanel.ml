(**************************************************************************)
(*                                                                        *)
(*  Author : Timothy Bourke                                               *)
(*  Organization : Synchronics, INRIA                                     *)
(*                                                                        *)
(**************************************************************************)

let _ = GMain.init () (* initialize lablgtk2 *)

let start_playing = ref true

let args =
  [
      ("-pause",
       Arg.Clear start_playing,
       "Start the simulator in paused mode.");
  ]

let destroy () = GMain.Main.quit ()

class periodic_task ~task_fn ~period_fn =
  object (self)
    val mutable deadline = max_float
    val mutable idle_id = GMain.Idle.add (fun () -> true)

    method private do_idle () =
      if Unix.gettimeofday() >= deadline then
        begin
          if not (task_fn ()) then self#stop ();
          deadline <- Unix.gettimeofday () +. period_fn ()
        end;
      true

    method start () =
      if deadline = max_float then idle_id <- GMain.Idle.add self#do_idle;
      deadline <- 0.0

    method stop () =
      if deadline != max_float then begin
        GMain.Idle.remove idle_id;
        deadline <- max_float
      end

    initializer
    GMain.Idle.remove idle_id
  end

let go period react_fn reset_fn =
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

  let min_period =
    if period = 0 then 0.0
    else max 0.2 (float period /. 40.0)

  and max_period =
    if period = 0 then 500.0
    else float period *. 40.0
  in

  let period = (min (max (float_of_int period) min_period) max_period) in

  let s_speed_adj = GData.adjustment
    ~lower:min_period
    ~upper:max_period
    ~value:period
    ~step_incr:1.0
    ()
  in

  let s_speed = GRange.scale
    `HORIZONTAL
    ~adjustment:s_speed_adj
    ~draw_value:false
    ~packing:outer_box#pack
    ()
  in
  ignore (s_speed); (* avoid compiler warning *)

  let run_react_fun () =
    try
      if Printexc.print react_fn () then begin
          b_single#misc#set_sensitive false;
          b_play#misc#set_sensitive false;
          b_pause#misc#set_sensitive false;
          false
        end else true
    with _ -> (destroy (); false) in

  let ptask = new periodic_task
    ~task_fn:run_react_fun
    ~period_fn:(fun () -> s_speed_adj#value /. 1000.0)
  in

  let step_react_fun () = ignore (run_react_fun ()) in

  let play_pushed () =
      b_single#misc#set_sensitive false;
      b_play#misc#set_sensitive false;
      b_pause#misc#set_sensitive true;
      ptask#start ()
  in

  let pause_pushed () =
      b_single#misc#set_sensitive true;
      b_play#misc#set_sensitive true;
      b_pause#misc#set_sensitive false;
      ptask#stop ()
  in

  ignore (b_play#connect#clicked ~callback:play_pushed);
  ignore (b_pause#connect#clicked ~callback:pause_pushed);
  ignore (b_single#connect#clicked ~callback:step_react_fun);

  if !start_playing then play_pushed ();

  ignore (w#connect#destroy ~callback:destroy);
  w#show ();
  GMain.Main.main ()

