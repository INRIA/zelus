(* compiles with -custom unix.cma    *)

(* instantiate a numeric solver *)
module Load = Loadsolvers
let () = Zlsolve.check_for_solver Sys.argv
module Runtime = (val Zlsolve.instantiate () : Zlsolve.ZELUS_SOLVER)

let go size model =
  let ss = ref (Runtime.main' size model) in
  let last_wall_clk = ref (Unix.gettimeofday ()) in

  let rec step signal =
    let result, delta, ss' = Runtime.step !ss in
    ss := ss';
    if Runtime.is_done !ss then ()
    else if delta <= 0.0 then step signal
    else
      let wall_clk = Unix.gettimeofday () in
      let delta' = delta -. (wall_clk -. !last_wall_clk) in
      (* NB: cut losses at each continuous step: *)
      last_wall_clk := wall_clk;
      if delta' <= 0.0 then step signal
      else (
        (* NB: accumulate losses across steps: *)
        (* wall_clk_last := wall_clk; *)
        Sys.set_signal Sys.sigalrm (Sys.Signal_handle step);
        ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_value = delta';
                                                  Unix.it_interval = 0.0 }))
  in
  step Sys.sigalrm;
  while not (Runtime.is_done !ss) do
    Unix.sleep 1
  done;
  exit(0)

