open Ztypes
open Sundials
   
type cstate =
       { mutable cvec: float array;
         mutable dvec: float array;
         mutable cstart: int;
         mutable cend: int;
         mutable zinvec: bool array;
         mutable zoutvec: float array;
         mutable discrete: bool;
         mutable horizon: float }

(* Lift a hybrid function (type 'a -C-> 'b) into a node ('a -D-> 'b) *)
let lift f =
  let cstate =
    { cvec = Array.make 0 0.0;
      dvec = Array.make 0 0.0;
      cstart = 0;
      cend = 0;
      zinvec = Array.make 0 false;
      zoutvec = Array.make 0 0.0;
      discrete = false;
      horizon = 0.0 } in

  let Node { alloc; step; reset }, cmax, zmax = f cstate in
  (* the vector of derivatives *)

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
  
  let yd = Array.make cmax 0.0 in
  let y = Array.make cmax 0.0 in
  
  (* the solver steps *)
  let s =
    Cvode.(init Adams Functional
             (SStolerances (1e-4, 1e-8)) f (zmax, g) 0.0 y) in

  Cvode.set_stop_time s 10.0;
  Cvode.set_all_root_directions s RootDirs.Increasing;

  let step s (t, r, x) =
    match r with
    | Cvode.Success -> Cvode.solve_normal s t y
    | Cvode.RootsFound ->
       ignore (step s t y zyin);
       Cvode.reinit s t y
    | Cvode.StopTimeReached -> next_t, r in

  let reset s = () in

  Node { alloc = alloc; step = step; reset = reset }
    
