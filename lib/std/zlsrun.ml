module Make (SSolver : Zls.STATE_SOLVER) =
struct

(* instantiate a numeric solver *)
module Solver = Zlsolve.Make (SSolver) (Illinois)

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

let go (Ztypes.Hsim { alloc      = main_alloc;
                      maxsize    = main_maxsize;
                      csize      = main_csize;
                      zsize      = main_zsize;
                      step       = main_step;
                      derivative = main_ders;
                      crossings  = main_zero;
                      reset      = main_reset;
                      horizon    = main_horizon; }) =
  let stepfn = Solver.step
        main_alloc
        main_csize
        main_zsize
        main_horizon
        main_maxsize
        main_ders
        main_step
        main_zero
        main_reset
  in

  let starting = ref (Unix.gettimeofday ()) in

  let rec step () =
    let _, is_done, delta = stepfn () in

    if is_done then ()
    else if delta = 0.0 then step ()
    else
      let ending = Unix.gettimeofday () in
      ignore (wait_next_instant !starting ending delta);
      starting := Unix.gettimeofday ();
      step ()
  in
  step ()

let check (Ztypes.Hsim { alloc      = main_alloc;
                         maxsize    = main_maxsize;
                         csize      = main_csize;
                         zsize      = main_zsize;
                         step       = main_step;
                         derivative = main_ders;
                         crossings  = main_zero;
                         reset      = main_reset;
                         horizon    = main_horizon; }) limit =
  let stepfn = Solver.step
        main_alloc
        main_csize
        main_zsize
        main_horizon
        main_maxsize
        main_ders
        main_step
        main_zero
        main_reset
  in
  let rec step n =
    if n == limit then ()
    else
      let result, is_done, delta = stepfn () in
      match result with
      | Some false -> exit 1
      | _ -> if is_done then () else step (n + 1)
  in
  (step 0; exit 0)

end

