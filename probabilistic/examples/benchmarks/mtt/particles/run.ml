open Benchlib

module M = struct
  type input = ((float * float) list) * ((float * float) list)
  type output = unit

  let read_input () =
    let process_list _ = 
      let process_list_helper fst =
        try
          Scanf.scanf "]";
          []
        with Scan_failure _ ->
          let this_elem = if fst then
            Scanf.scanf "(%f, %f)" (fun x y -> (x, y)) 
          else 
            Scanf.scanf ",(%f, %f)" (fun x y -> (x, y)) 
          in
          this_elem :: (process_list false)
      in
      Scanf.scanf "[";
      process_list_helper true
    in

    let truth = process_list () in
    Scanf.scanf " : ";
    let obs = process_list () in
    (truth, obs)

  let main = Mtt_particles.main
end

module H = Harness.Make(M)

let () =
  H.run ()
