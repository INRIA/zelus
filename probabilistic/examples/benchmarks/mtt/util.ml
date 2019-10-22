open Owl

let list_init = List.init

let p_dead = 1. (* XXX TODO XXX *)

let mu_new = (* XXX TODO XXX *)
  Mat.of_arrays [| [| 0.; |];
                   [| 1.; |]; |]

let sigma_new = (* XXX TODO XXX *)
  Mat.of_arrays [| [| 1.0; 0.8; |];
                   [| 0.8; 1.0; |] |]

let a_u = (* XXX TODO XXX *)
  Mat.of_arrays [| [| 1.0; 0.8; |];
                   [| 0.8; 1.0; |] |]

let b_u = (* XXX TODO XXX *)
  Mat.of_arrays [| [| 0.; |];
                   [| 1.; |]; |]

let sigma_update = (* XXX TODO XXX *)
  Mat.of_arrays [| [| 1.0; 0.8; |];
                   [| 0.8; 1.0; |] |]


let mu_clutter = (* XXX TODO XXX *)
  Mat.of_arrays [| [| 0.; |];
                   [| 1.; |]; |]

let sigma_clutter = (* XXX TODO XXX *)
  Mat.of_arrays [| [| 1.0; 0.8; |];
                   [| 0.8; 1.0; |] |]


let mu_init = (* XXX TODO XXX *)
  Mat.of_arrays [| [| 0.; |];
                   [| 1.; |]; |]

let sigma_init = (* XXX TODO XXX *)
  Mat.of_arrays [| [| 1.0; 0.8; |];
                   [| 0.8; 1.0; |] |]


let shuffle x = x

let ( *@ ) = Mat.( *@ )
let ( +@ ) = Mat.add
