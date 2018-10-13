open Ztypes
(* simulation (discrete) function *)
let main = let Node { alloc = alloc; step = step; reset = reset } = Heat.main in 
           let mem = alloc () in reset mem;fun _ -> step mem ();;
(* simulation loop: sampled on period 0.100000 Hz *)

(* instantiate the discrete interface *)
module Runtime = Zlsrungtk.MakeDiscrete ()
let _ = Runtime.go 0.100000 main
