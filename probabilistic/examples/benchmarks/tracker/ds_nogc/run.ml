open Benchlib

module M = struct
    type input = unit
    type output = unit
    let iters = ref 0
    let read_input () =
        begin
            if !iters >= 1600 then
                raise End_of_file
            else
                iters := !iters + 1
        end;
        ()
    let main = Tracker_ds_nogc.main
end

module H = Harness.Make(M)

let () =
    H.run ()
