open Owl

let concat_vertical = Mat.concat_vertical
let concat_horizontal = Mat.concat_horizontal
let of_lists l = Mat.of_arrays (Array.of_list (List.map Array.of_list l))
let eye = Mat.eye
let zeros = Mat.zeros
let mul_scalar = Mat.mul_scalar
let dot = Mat.dot
let add = Mat.add
let diagm = Mat.diagm
let get = Mat.get

let dare = Linalg.D.dare
let transpose = Mat.transpose
let linsolve = Linalg.D.linsolve

open Owl_plplot

let plot file y =
  let h = Plot.create file in
  Plot.set_page_size h 500 400;
  let n, m = Mat.shape y in
  let x = Mat.sequential n 1 in
  Plot.plot ~h ~spec:[ RGB (150,0,0) ] x (Mat.col y 0);
  Plot.plot ~h ~spec:[ RGB (0,150,0) ] x (Mat.col y 1);
  Plot.plot ~h ~spec:[ RGB (0,0,150) ] x (Mat.col y 2);
  Plot.output h;
