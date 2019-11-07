open Owl
open Owl_plplot

let of_lists l = Mat.of_arrays (Array.of_list (List.map Array.of_list l))
let of_list l n m = Mat.of_array (Array.of_list l) n m

let plot file y =
  let h = Plot.create file in
  Plot.set_page_size h 500 400;
  let n, m = Mat.shape y in
  let x = Mat.sequential n 1 in
  Plot.plot ~h ~spec:[ RGB (150,0,0) ] x (Mat.col y 0);
  Plot.plot ~h ~spec:[ RGB (0,150,0) ] x (Mat.col y 1);
  Plot.plot ~h ~spec:[ RGB (0,0,150) ] x (Mat.col y 2);
  Plot.output h;