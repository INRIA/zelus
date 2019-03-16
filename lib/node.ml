(* ocamlfind ocamlc bigarray.cma sundials.cma cvode.ml -package sundialsml *)
open Ztypes
open Bigarray
open Sundials
   
(* The interface with the solver *)
type cstate =
  { mutable dvec : dvec; (* the vector of derivatives *)
    mutable cvec : cvec; (* the vector of positions *)
    mutable zinvec : zinvec; (* the vector of boolean; true when the
                             solver has detected a zero-crossing *)
    mutable zoutvec : zoutvec; (* the corresponding vector that define
                               zero-crossings *)
    mutable cstart : int; (* the start position in the vector of positions *)
    mutable zstart : int; (* the start position in the vector of zero-crossings *)
    mutable cend : int; (* the maximum size of the vector of positions *)
    mutable zend : int; (* the maximum number of zero-crossings *)
    mutable horizon : float; (* the next horizon *)
    mutable discrete : bool; (* integration iff [discrete = false] *)
  }
  
(* Lift a hybrid function (type 'a -C-> 'b) into a node ('a -D-> 'b) *)
let go f stop_time =
  let cstate =
    { cvec = Array1.create Float64 c_layout 0;
      dvec = Array1.create Float64 c_layout 0;
      cstart = 0;
      cend = 0;
      zstart = 0;
      zend = 0;
      zinvec = Array1.create Int32 c_layout 0;
      zoutvec = Array1.create Float64 c_layout 0;
      discrete = false;
      horizon = 0.0 } in

  (* create a node *)
  let Node { alloc; step; reset }, cmax, zmax = f cstate in
  
  (* the derivative *)
  let f s time y yd =
    cstate.cvec <- y;
    cstate.dvec <- yd;
    ignore (step s input) in
  
  (* the zero-crossing function *)
  let g s time y zyout =
    cstate.cvec <- y;
    cstate.zoutvec <- zyout;
    ignore (step s input) in
  
  (* the step function *)
  let step s time y zyin =
    cstate.cvec <- y;
    cstate.zinvec <- zyin;
    ignore (step s input) in
  
  let yd = RealArray.make cstate.cend 0.0 in
  let y = Nvector_serial.wrap yd in
  
  (* the solver steps *)
  let s =
    Cvode.(init Adams Functional
             (SStolerances (1e-4, 1e-8)) f ~roots:(cstate.zend, g) 0.0 y) in

  Cvode.set_stop_time s 10.0;
  Cvode.set_all_root_directions s RootDirs.Increasing;

  let step s (t, r, x) =
    match r with
    | Cvode.Success -> Cvode.solve_normal s t y
    | Cvode.RootsFound ->
       ignore (step s t y zyin);
       Cvode.reinit s Cvode.Adams (zmax, g) t y
    | Cvode.StopTimeReached -> next_t, r in

  let reset s = () in

  Node { alloc = alloc; step = step; reset = reset }
    
