(* compiles with -custom unix.cma    *)

(* instantiate a numeric solver *)
module Load = Loadsolvers
let () = Zlsolve.check_for_solver Sys.argv
module Runtime = (val Zlsolve.instantiate () : Zlsolve.ZELUS_SOLVER)

let wake_me f =
  let rec step signal =
    match f () with
    | None -> raise Exit
    | Some delta ->
        (Sys.set_signal Sys.sigalrm (Sys.Signal_handle step);
         ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_value = delta;
                                                  Unix.it_interval = 0.0 }))
  in
  step Sys.sigalrm;
  try
    while true do
      Unix.sleep 6000
    done
  with Exit -> exit 0

let go size model =
  let ss = ref (Runtime.main' size model) in
  let last_wall_clk = ref (Unix.gettimeofday ()) in

  let rec delay () =
    let result, delta, ss' = Runtime.step !ss in
    let wall_clk = Unix.gettimeofday () in
    let delta' = delta -. (wall_clk -. !last_wall_clk) in
    ss := ss';
    last_wall_clk := wall_clk;

    if Runtime.is_done !ss then None
    else if delta <= 0.0 then delay ()
    else
      (* NB: cut losses at each continuous step: *)
      if delta' <= 0.0 then delay ()
      else Some delta' (* NB: accumulate losses across steps: *)
  in
  wake_me delay

