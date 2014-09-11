(* compiles with -custom unix.cma    *)

(* instantiate a numeric solver *)
module Load = Loadsolvers
let () = Zlsolve.check_for_solver Sys.argv
module Runtime = (val Zlsolve.instantiate () : Zlsolve.ZELUS_SOLVER)

(*** Timer version ***)
(* let wait_next_instant debut fin min = *)
(*   let diff = min -. (fin -. debut) in *)
(*   let rec step signal = *)
(*     if diff > 0.0 then *)
(*       (Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Exit)); *)
(*        ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_value = diff; *)
(*                                                  Unix.it_interval = 0.0 })) *)
(*     else raise Exit *)
(*   in *)
(*   try *)
(*     step Sys.sigalrm; *)
(*     while true do *)
(*       Unix.sleep 6000 *)
(*     done *)
(*   with Exit -> () *)

(*** Without error handling ***)
(* let rec wait_next_instant debut fin min = *)
(*   let diff = min -. (fin -. debut) in *)
(*   if diff > 0.0 then *)
(*     begin try *)
(*       ignore (Unix.select [] [] [] diff); false *)
(*     with Unix.Unix_error (Unix.EINTR ,_, _) -> *)
(*       wait_next_instant debut (Unix.gettimeofday ()) min *)
(*     end *)
(*   else true *)

let wait_next_instant =
  let delay = ref 0.0 in

  let rec wait_next_instant starting ending delta =
    let diff = (delta -. (ending -. starting)) -. !delay in
    if diff > 0.0 then
      begin try
        delay := 0.0;
        ignore (Unix.select [] [] [] diff); false
      with Unix.Unix_error (Unix.EINTR ,_, _) ->
        wait_next_instant starting (Unix.gettimeofday ()) delta
      end
    else
      begin
        delay := min (-. diff) delta;
        true
      end
  in
  wait_next_instant

let go size model =
  let ss = ref (Runtime.main' size model) in
  let starting = ref (Unix.gettimeofday ()) in

  let rec step () =
    let result, delta, ss' = Runtime.step !ss in
    ss := ss';

    if Runtime.is_done !ss then ()
    else if delta = 0.0 then step ()
    else
      let ending = Unix.gettimeofday () in
      ignore (wait_next_instant !starting ending delta);
      starting := Unix.gettimeofday ();
      step ()
  in
  step ()

