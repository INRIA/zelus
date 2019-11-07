open Benchlib
open Owl

module M = struct
  type input = (Mat.mat list) * (Mat.mat list)
  type output = unit

  let read_input () =
    let mk_vec a b =
        Mat.of_arrays [| [| a |];
                         [| b |] |]
    in
    let process_list _ = 
      let rec process_list_helper fst =
        try
          Scanf.scanf "]" (fun _ -> ()) 0;
          []
        with Scanf.Scan_failure _ ->
          let this_elem = if fst then
            Scanf.scanf "(%f, %f)" (fun x y -> mk_vec x y) 
          else 
            Scanf.scanf ",(%f, %f)" (fun x y -> mk_vec x y) 
          in
          this_elem :: (process_list_helper false)
      in
      Scanf.scanf "[" (fun _ -> ()) 0;
      process_list_helper true
    in

    let truth = process_list () in
    Scanf.scanf " : " (fun _ -> ()) 0;
    let obs = process_list () in
    (truth, obs)

  let main = Mtt_particles.main
end

module H = Harness.Make(M)

let () =
  H.run ()
