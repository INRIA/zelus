open Benchlib
open Slamlib

module M = struct
  type input = bool array * unit
  type output = unit

  let read_input () =
    let a = Array.make (Array_misc.max_pos + 1) false in
    for i = 0 to Array_misc.max_pos do
      a.(i) <- Scanf.scanf "%B, " (fun x -> x)
    done;
    a, ()

  let main = Slam_ds_nogc.main
end

module H = Harness.Make(M)

let () =
  H.run ()
