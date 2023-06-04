(*
  Implementation of a simple pattern described in Hiebert and Shampine,
  ``Implicitly Defined Output Points for Solutions of ODEs'', 1980.

  Plot a table of solutions of a system of ordinary differential equations with
  increments taken in a dependent variable.

  The details of the system are immaterial (and not given by the paper). It is
  the pattern and its expression that are interesting.
*)

let node print_header () =
  let _ = print_string "\t      x" in
  let _ = print_string "\t\ty(x)" in
  print_newline ()

let node print_line (x, y) =
  let _ = print_string "\t" in
  let _ = print_float x in
  let _ = print_string "\t" in
  let _ = print_float y in
  print_newline ()

let hybrid system () = y where
  rec der t = 1.0 init 0.0
  and der y = exp(t) *. sin (10.0 *. t) init -1.0

let hybrid tabulate_dependent () = let
  rec der x = 1.0 init 0.0
  and y = system ()

  and init c = 1.0
  and present
      z -> do c = (last c +. 1.0) done

  and z = up(y -. last c)
  
  in present
     | z -> let () = (print_header ()) -> () in
            print_line (x, y)
     else ()
  
let hybrid main () =
  tabulate_dependent ()

