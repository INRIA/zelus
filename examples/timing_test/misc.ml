let start = Unix.gettimeofday ()

let get_time () = Unix.gettimeofday () -. start

let print (d1, d2) =
 Printf.sprintf
    "Time = %.12e\t Diff = %.12e\t" d1 d2
