(* compiles with -custom unix.cma    *)

(* instantiate a numeric solver *)
module Load = Loadsolvers
let () = Zlsolve.check_for_solver Sys.argv
module Runtime = (val Zlsolve.instantiate () : Zlsolve.ZELUS_SOLVER)

let go size model =
  let ss = ref (Runtime.main' size model) in
  let last_wall_clk = ref (Unix.gettimeofday ()) in

  let rec step () =
    let result, delta, ss' = Runtime.step !ss in
    let wall_clk = Unix.gettimeofday () in
    let delta' = delta -. (wall_clk -. !last_wall_clk) in
    ss := ss';
    last_wall_clk := wall_clk;

    if Runtime.is_done !ss then ()
    else if delta <= 0.0 then  step ()
    else
      (* NB: cut losses at each continuous step: *)
      if delta' <= 0.0 then step ()
      else (
        (* NB: accumulate losses across steps: *)
        ignore (Unix.select [] [] [] delta');
        step ())
  in
  step ();
  exit(0)
