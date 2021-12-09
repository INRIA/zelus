(* Tester les initialisations *)

(*let hybrid f(c, z) = k where
  rec init x = 0.0 and der k = last x +. 1.0
*)

let hybrid g(c,z) = () where
  rec match c with
      | true -> local x in
                do der x = 1.0 and init x = 0.0 done
                (* let rec der x = 1.0 and init x = 0.0 in do done *)
                (* local x in do der x = 1.0 and init x = 2.0 done *)
                (*local y in local x in do x = 1
                and der y = 1.0 init 0.0 done *)
      | _ -> let rec der x = 1.0 and init x = 0.0 in do done
  
(*
let hybrid f(c, z) = x where
  rec automaton
      | S1 -> do x = 1.0 until z then S2 done
      | S2 -> do der x = 2.0 done
*)

(*
let hybrid f(c, z) = x where
  rec match c with
      | true -> do der x = 1.0 reset 2.0 every z done
      | _ -> do done
  and init x = 0.0

let hybrid g(c) = x where
  rec der x = 1.0 and x = 2.0 every c init 0.0
*)

(* 

last_v = false -> lv and lv = pre(v) and v = if upb(x) then last_o else last_v
and last_o = pre(o)

let f(x) = y where
  automaton
  | S1 -> do y = 1 -> last y + 1
          until 
*)

(*
let node f(c) = o where rec
   match c with
   | true -> do x = 1.0 and last_x = 0.0 -> lx done
   | false -> do x = 2.0 and last_x = 1.0 -> lx done
   and
   lx = pre(x)

let hybrid f(c) = o where rec
   match c with
   | true -> do der x = 1.0 init 0.0 done
   | false -> do der x = 2.0 init 1.0 done

let node f(c) = o where rec
  match x with
  | true -> do dx = 1.0 and last_x = 0.0 -> lx done
  | false -> do dx = 2.0 and last_x = 1.0 -> lx done
  and
  x = if d then lx else last_x

let hybrid f () = o where rec
   automaton
   | S1 -> do der x = 1.0 init 0.0
           until up(x -. 10.0) then S2(0.0) done
   | S2(x0) -> do der x = -1.0 init x0 done

let hybrid avoidance (x_i, y_i, theta_i, v_1, v_2) = (x, y, theta, t) where
  rec theta = theta_i
  and init t = 0.0
  and automaton
      | Start -> do then Cruise(x_i,y_i)
      | Cruise(x0,y0) ->
          do
            der t = 0.0
            and der x = x' init x0
            and der y = y' init y0
          until (up(sqr(alpha1) -. sqr(x) -. sqr(y)))
          then Left(rotate(-. delta_phi, x, y) )
          done

      | Left(x0, y0) ->
          local t1, t2 in
          do
                t1 = d /. (v_1 *. sin(delta_phi))
            and t2 = d /. (v_2 *. sin(delta_phi))
            and der t = 1.0
            and der x = x' init x0
            and der y = y' init y0
          until (up(t -. max(t1, t2)))
          then Straight(rotate(delta_phi, x, y))
          done

      | Straight(x0,y0) -> do
            der t = 0.0
            and der x = x' init x0
            and der y = y' init y0
          until (up(sqr(x) +. sqr(y) -. sqr(alpha2)))
          then Right(rotate(delta_phi, x, y))
          done

      | Right(x0,y0) -> do
            der t = -. 1.0
            and der x = x' init x0
            and der y = y' init y0
          until (up(-. t))
          then Cruise(rotate(-. delta_phi, x, y))
          done
  and x' = -. v_1 +. v_2 *. cos(theta)
  and y' = v_2 *. sin(theta)
*)

(* der in nested let/in containing a match *)

(*
let hybrid nested z = x where
  x = (let init y = 0.0
           and match z with
               | true ->  do der y =  1.0 done
               | false -> do der y = -1.0 done
       in y) +. 2.0

let hybrid main () =
  let x = nested true in
  ()
*)
