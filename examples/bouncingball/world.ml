
let ground_height =
  [|
    5.0;
    4.0;
    3.0;
    2.0;
    1.0;
    0.0;
  |]
let ground_limits = [| 1.0; 3.0; 4.0; 6.0; 8.0; 20.0 |]
let ground_maxidx = Array.length ground_height - 1

let lookup_limit x =
  let rec f idx =
    if idx = ground_maxidx || x < ground_limits.(idx) then idx
    else f (idx + 1)
  in f 0

let ground x = ground_height.(lookup_limit x)
let ground_abs x = ground_limits.(lookup_limit x)

let show_trace = ref false

(*
let () = Zlsolve.add_custom_arg
    ("-trace", Arg.Set show_trace,
     " Show a trace of ball positions.")
 *)

let () = Showball.start !show_trace (ground_height, ground_limits)

