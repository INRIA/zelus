open Benchlib

module M = struct
  type input = (float * float) * float
  type output = float * float
  let read_input () = Scanf.scanf ("%f, %f, %f\n") (fun mu sigma y -> ((mu, sigma), y))
let main = Gaussian_ds.main
end

module H = Harness.Make(M)

let () =
  H.run ()
