
let ground_height =
  [|
    3.0
  |]
let ground_limits = [| 10.0 |]
let ground_maxidx = Array.length ground_height - 1

let lookup_limit x =
  let rec f idx =
    if idx = ground_maxidx || x < ground_limits.(idx) then idx
    else f (idx + 1)
  in f 0

let ground x = ground_height.(lookup_limit x)
let ground_abs x = ground_limits.(lookup_limit x)

let show_trace = ref false

let () = Showball.start !show_trace (ground_height, ground_limits)

