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

  let Node { alloc; step; reset } = f cstate in
  (* the vector of derivatives *)

  (* the derivative *)
  let f s time y yd =
    cstate.cvec <- y;
    cstate.dvec <- yd;
    ignore (step s input) in
  
  (* the zero-crossing function *)
  let g s time y yd =
    cstate.cvec <- y;
    cstate.zvec <- yd;
    ignore (step s input) in
  
  (* the step function *)
  let step s time y yd =
    cstate.cvec <- y;
    cstate.zvec <- yd;
    ignore (step s input) in
  
  let yd = Array.make cmax 0.0 in
  let y = Array.wrap yd in
  
  (* the solver steps *)
  let s =
    Cvode.(init Adams Functional
             (SStolerances (1e-4, 1e-8)) f (zmax, g) 0.0 y) in

  let step s (t, r, x) =
    let next_t, r = Cvode.solve_normal s t y in
    match r with
    | Cvode.Success ->
    | Cvode.RootsFound ->
    | Cvode.StopTimeReached -> next_t, r in

  let reset s = () in

  Node { alloc = alloc; step = step; reset = reset }
    
