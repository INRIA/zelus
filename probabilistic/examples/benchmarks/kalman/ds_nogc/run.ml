open Benchlib

module M = struct
  type input = float * float
  type output = float
  let read_input () = Scanf.scanf ("%f, %f\n") (fun t o -> (t, o))
  let main = Kalman_ds_nogc.main
end

module H = Harness.Make(M)

let () =
  H.run ()
