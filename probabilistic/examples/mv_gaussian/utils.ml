open Owl

let mu = Mat.of_arrays [| [| 0.; |];
                          [| 1.; |]; |]

let sigma x = Mat.of_arrays [| [| 1.0; x; |];
                               [| x; 1.0; |] |]

let display_point v =
  let x = Arr.get v [|0; 0|] in
  let y = Arr.get v [|1; 0|] in
  Graphics.plot
    (int_of_float (100. *. x +. 400.))
    (int_of_float (100. *. y +. 400.))

let display_mvg d =
  Graphics.clear_graph ();
  Graphics.draw_segments [| 400, 0, 400, 800 |];
  Graphics.draw_segments [| 0, 400, 800, 400 |];
  for _ = 1 to 10_000 do
    let v = Distribution.draw d in
    display_point v
  done;
  Graphics.synchronize ()

let () =
  Graphics.open_graph " 800x800";
  Graphics.set_window_title "Multivariate Gaussian";
  Graphics.auto_synchronize false
