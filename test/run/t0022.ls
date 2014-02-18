(* TEST[-check 100] *)

(* 
   When this program enters state Free, x should be higher than 400
   and y higher than 200. 

   Currently, y does not take the correct value. Note that the problem
   disappears if we remove up(100.). The problem is due to the
   incorrect compilation of state parameters. 
*)

let hybrid ball () = (x,y) where
  rec automaton
      | Init -> 
	  do der y = 1. init 0.
	  and der x = 1. init 0. 
	  until (period(0.1)) then Free(400., 200.) done
      | Free(x0,y0) -> 
	  do der x = 1. init x0
	  and der y = 1. init y0 
	  until up(100.) then Free(x,y)  done 

let hybrid main () = obs where
  rec (x,y) = ball() 
  and obs = present (period(0.2)) -> (x > 400. && y > 200.) else true 
