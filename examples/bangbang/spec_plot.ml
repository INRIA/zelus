open Ztypes
open Zls
(* simulation (continuous) function *)
let main = let Hybrid { alloc = alloc; step = hstep; reset = reset } = Spec.plot in 
           let step mem c d zin t = discrete := true; cvec := c;dvec := d; zinvec := zin;cindex := 0; zindex := 0;horizon := infinity; hstep mem (t, ()) in
           let derivative mem c d zin zout t = discrete :=false; cvec := c; dvec := d;zinvec := zin; zoutvec := zout;cindex := 0; zindex := 0;hstep mem (t, ()) in
           let crossings mem c zin zout t =  discrete := false; cvec := c;zinvec := zin; zoutvec := zout;cindex := 0; zindex := 0;hstep mem (t, ()) in
           let maxsize mem = (!cmax, !zmax) in
           let csize mem = !cindex in
           let zsize mem = !zindex in
           let horizon mem = !horizon in
           Hsim {alloc; step; reset; derivative; crossings; maxsize; csize; zsize; horizon};;
(* instantiate a numeric solver *)
module Runtime = Zlsrungtk.Make (Defaultsolver)
let _ = Runtime.go main
