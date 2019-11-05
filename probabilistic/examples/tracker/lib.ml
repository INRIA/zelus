open Owl

type mat = Owl.Mat.mat
type vec = Owl.Mat.mat

let a = Mat.of_arrays
    [| [| 1.0; 0.1; 0.0 |] ;
       [| 0.0; 1.0; 0.1 |] ;
       [| 0.0; 0.0; 0.0 |] |]

let a_approx = Mat.of_arrays
    [| [| 1.0; 0.1; 0.0 |] ;
       [| 0.0; 1.0; 0.1 |] ;
       [| 0.0; 0.0; 0.000001 |] |]

let b = Mat.eye 3

let q = Mat.of_arrays
    [| [| 1.0; 0.0; 0.0; |] ;
       [| 0.0; 0.1; 0.0; |] ;
       [| 0.0; 0.0; 0.1; |] |]

let r = Mat.of_arrays
    [| [| 1000.; 0.0  ; 0.0; |] ;
       [| 0.0  ; 1000.; 0.0; |] ;
       [| 0.0  ; 0.0  ; 1.0; |] |]

let n = Mat.zeros 3 3

let x_init = Mat.of_array [| 0.0; 0.0; 0.0 |] 3 1
let zerost = Mat.zeros 3 1

let init_sig = Mat.of_arrays
    [| [| 100.0; 0.0; 0.0 |] ;
       [| 0.0; 100.0; 0.0 |] ;
       [| 0.0; 0.0; 100.0 |] |]


let update_sig = Mat.of_arrays
    [| [| 0.1; 0.0; 0.0 |] ;
       [| 0.0; 0.1; 0.0 |] ;
       [| 0.0; 0.0; 0.1 |] |]

let obs_acc = Mat.of_arrays
    [| [| 0.0; 0.0; 0.0 |] ;
       [| 0.0; 0.0; 0.0 |] ;
       [| 0.0; 0.0; 1.0 |] |]

let obs_acc_approx = Mat.of_arrays
    [| [| 0.0001; 0.0; 0.0 |] ;
       [| 0.0; 0.0001; 0.0 |] ;
       [| 0.0; 0.0; 1.0 |] |]

let obs_acc_gps = Mat.of_arrays
    [| [| 1.0; 0.0; 0.0 |] ;
       [| 0.0; 0.0; 0.0 |] ;
       [| 0.0; 0.0; 1.0 |] |]

let obs_acc_gps_approx = Mat.of_arrays
    [| [| 1.0; 0.0; 0.0 |] ;
       [| 0.0; 0.0001; 0.0 |] ;
       [| 0.0; 0.0; 1.0 |] |]

let obs_sig = Mat.of_arrays
    [| [| 1.0; 0.0; 0.0 |] ;
       [| 0.0; 1.0; 0.0 |] ;
       [| 0.0; 0.0; 0.1 |] |]

let mul = Owl.Mat.dot
let add = Owl.Mat.add

let state_tostring st =
  "[ " ^ string_of_float (Owl.Mat.get st 0 0) ^ ", " ^ string_of_float (Owl.Mat.get st 1 0) ^ ", " ^ string_of_float (Owl.Mat.get st 2 0) ^ "]"

let get_pos st = Owl.Mat.get st 0 0

let print = Owl.Mat.print

open Owl
open Owl_plplot


let res = ref (Mat.zeros 1 3)
let add_result (xt, yt, xest) =
  let v = Mat.of_arrays [|[|xt; yt; xest|]|] in
  res := Mat.(!res @= v)

let h = Plot.create "plot_3pos.pdf";;
Plot.set_page_size h 500 400

let exit_and_plot () =
  let n, m = Mat.shape !res in
  let x = Mat.sequential n 1 in
  Format.printf "XXXXXXXXX@.";
  Plot.plot ~h ~spec:[ RGB (150,0,0) ] x (Mat.col !res 0);
  Plot.plot ~h ~spec:[ RGB (0,150,0) ] x (Mat.col !res 1);
  Plot.plot ~h ~spec:[ RGB (0,0,150) ] x (Mat.col !res 2);
  Plot.output h;
  (* exit 0 *)
