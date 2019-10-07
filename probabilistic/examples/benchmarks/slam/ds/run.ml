module M = struct
  type input = (bool array * int) * (bool * int)
  type output = unit

  let read_input () =
    let a = Array.make (Array_misc.max_pos + 1) false in
    for i = 0 to Array_misc.max_pos do
      a.(i) <- Scanf.scanf "%B, " (fun x -> x)
    done;
    let x = Scanf.scanf "%d, " (fun x -> x) in
    let obs = Scanf.scanf "%B, " (fun x -> x) in
    let cmd = Scanf.scanf "%d\n" (fun x -> x) in
    (a, x), (obs, cmd)

  let main = Slam_ds.main
end

module H = Harness.Make(M)

let () =
  H.run ()
