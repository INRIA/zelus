open Ztypes
open Zls

(* simulation (continuous) function *)
let main = 
  let cstate = 
    { dvec = cmake 0; cvec = cmake 0; zinvec = zmake 0; zoutvec = cmake 0; 
      cindex = 0; zindex = 0; cend = 0; zend = 0; cmax = 0; zmax = 0; 
      major = false; horizon = 0.0 } in 
  let Node { alloc = alloc; step = hstep; reset = reset } = Flatball.main cstate in 
  let step mem cvec dvec zin t = 
    cstate.major <- true; cstate.cvec <- cvec; cstate.dvec <- dvec; 
    cstate.cindex <- 0; cstate.zindex <- 0; cstate.horizon <- infinity;  
    hstep mem (t, ()) in
  let derivative mem cvec dvec zin zout t = 
    cstate.major <- false;  cstate.cvec <- cvec; cstate.dvec <- dvec; 
    cstate.zinvec <- zin; cstate.zoutvec <- zout; cstate.cindex <- 0; 
    cstate.zindex <- 0; ignore (hstep mem (t, ())) in
  let crossings mem cvec zin zout t = 
    cstate.major <- false;  cstate.cvec <- cvec; cstate.zinvec <- zin; 
    cstate.zoutvec <- zout; cstate.cindex <- 0; cstate.zindex <- 0; 
    ignore (hstep mem (t, ())) in
  let maxsize mem = cstate.cmax, cstate.zmax in
  let csize mem = cstate.cend in
  let zsize mem = cstate.zend in
  let horizon mem = cstate.horizon in
  Hsim { alloc; step; reset; derivative; crossings; maxsize;  csize;  zsize; 
         horizon };;
(* instantiate a numeric solver *)
module Runtime = Zlsrun.Make (Defaultsolver)
let _ = Runtime.go main
