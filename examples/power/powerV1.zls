(* Simulation of power consumption *)

let t0 = 0.0
let tmax = 7.0
let hyst = 6.0
let r = 1000.0
let c = 10e-5

let hybrid power() = (p, t, cpt) where
 rec der t = (p /. c) -. (t /. (r *. c)) init t0
 and init cpt = -0.030
 and automaton
     | High ->
        do p = 0.01
        and der cpt = 1.0
        until up(cpt) then do next cpt = -0.020 in Low
         else up(t -. tmax) then Sleep
     | Low ->
         do p = 0.005
         and der cpt = 1.0
         until up(cpt) then do next cpt = -0.030 in High 
          else up(t -. tmax) then Sleep
     | Sleep ->
         do p = 0.0
         until up((tmax -. hyst) -. t)
          then do next cpt = -0.020 in Low
  
(* Main entry point *)
let hybrid main () =
        let der time = 1.0 init 0.0 in 
        let (p, t, cpt) = power () in
        present (period (0.001)) ->
        let s = Scope.scope3 (-0.5, 1.2,
                        ("p", Scope.linear, 10.0 *. p),
                        ("t", Scope.linear, t /. 10.0),
                        ("cpt", Scope.linear, 2.0 *. cpt)
                ) in
                Scope.window ("powerv1", 0.5, time, s)
        else ()


