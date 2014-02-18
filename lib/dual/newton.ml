(*
 *
 * Newton-Raphson method: solves g(x)=0 starting from x0
 * Returns x such that - eps <= g(x) <= eps
 * Raises Not_found whenever x, g(x) or d g(x) / dx becomes nan, infinity or neg_infinity
 * Raises Not_found if x goes out of interval [x0 -. radius; x0 +. radius]
 *
 *)

let debug x y =
  begin
    Printf.fprintf stderr "x=%f y=%s " x (Dual.string_of_dual y);
    flush stderr
  end

let is_overflow x =
  match classify_float x with
      FP_nan | FP_infinite -> true
    | _ -> false

let solve eps radius g x0  =
  let x = ref x0
  and y = ref (g (Dual.make x0 1.)) in
    begin
      while (abs_float (Dual.re (!y))) > eps
      do
	(* debug (!x) (!y); *)
	if (is_overflow (!x)) || (is_overflow (Dual.re (!y))) || (is_overflow (Dual.im (!y))) || ((abs_float ((!x) -. x0)) > radius)
	then raise Not_found
	else
	  let d = (Dual.re (!y)) /. (Dual.im (!y)) in
	    begin
	      (* Printf.fprintf stderr "d=%f\n" d; *)
	      (* flush stderr; *)
	      if (abs_float (d /. (!x))) < epsilon_float
	      then raise Not_found
	      else
		begin
		  x := (!x) -. d;
		  y := (g (Dual.make (!x) 1.))
		end
	    end
      done;
      !x
    end
      
(*
 *
 * Gauss-Newton method: solves g(x,y)=0 such that (x-x0)^2 + (y-y0)^2 is minimal
 * Returns (x,y) such that - eps <= g(x,y) <= eps
 * Raises Not_found whenever (x,y), g(x,y) or d g(x,y)/dx or dy becomes nan, infinity or neg_infinity
 * Raises Not_found if (x,y) goes out a the disc or a given radius centered on (x0,y0)
 *
 *)

let eudis x y x0 y0 = sqrt ((x -. x0) *. (x -. x0) +. (y -. y0) *. (y -. y0))

let solve2 eps radius g x0 y0 =
  let x = ref x0
  and y = ref y0
  and z = ref (Dual.re (g (Dual.const x0) (Dual.const y0))) in
    begin
      while (abs_float (!z)) > eps do
	(* Printf.fprintf stderr "x=%f y=%f z=%f" (!x) (!y) (!z); *)
	(* flush stderr; *)
	let dz_dx = Dual.im (g (Dual.make (!x) 1.) (Dual.const (!y)))
	and dz_dy = Dual.im (g (Dual.const (!x)) (Dual.make (!y) 1.)) in
	  if (is_overflow (!x)) || (is_overflow (!y)) || (is_overflow (!z)) ||
	    (is_overflow dz_dx) || (is_overflow dz_dy) || ((eudis (!x) (!y) x0 y0) > radius)
	  then raise Not_found
	  else
            (*
	     *
	     * Find dx and dy such that dx *. dz_dx +. dy *. dz_dy = z and
	     * dx *. dx + dy *. dy is minimal
	     * 
	     *)
	    let n = dz_dx *. dz_dx +. dz_dy *. dz_dy in
	    let dx = dz_dx *. (!z) /. n
	    and dy = dz_dy *. (!z) /. n in
	      if ((abs_float (dx /. (!x))) < epsilon_float) &&
		((abs_float (dy /. (!y))) < epsilon_float)
	      then raise Not_found
	      else
		begin
		  (* Printf.fprintf stderr " dx=%f dy=%f\n" dx dy; *)
		  (* flush stderr; *)
		  x := (!x) -. dx;
		  y := (!y) -. dy;
		  z := Dual.re (g (Dual.const (!x)) (Dual.const (!y)))
		end
      done;
      ((!x),(!y))
    end
