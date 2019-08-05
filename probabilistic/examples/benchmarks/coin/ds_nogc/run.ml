module M = struct
  type input = float * bool
  type output = float
  let read_input () = Scanf.scanf ("%f, %B\n") (fun t o -> (t, o))
  let main = Coin_ds_nogc.main
end

module H = Harness.Make(M)

let () =
  H.run ()
