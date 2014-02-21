(* Simulate with: -sundialsI -maxt 2 *)

(* car1 going from Barcelona to Girona *)
(* car2 going from Girona to Barcelona *)
let barcelona = 0.0
let girona = 100.0

let fly_velocity = 80.0
let car_velocity = 50.0

(* The main system.*)
(* It returns the position of the two cars, the fly. [zeros] is *)
(* the number of zigzags. [zigzag] is an event present when a zigzag occurs *)
let hybrid model () =  (car1, car2, fly, zigzag, zeros) where
  rec der car1 = car_velocity init barcelona
  and der car2 = -. car_velocity init girona
  and der fly = dir *. fly_velocity init barcelona
  and automaton
      | Above -> do car_above = car2 and car_below = car1
                 until up(car1 -. car2) then Below
      | Below -> do car_above = car1 and car_below = car2 done
      end
  and present 
         up (car_below -. fly) | up(fly -. car_above) -> 
           do dir = -. (last dir)
           and zeros = last zeros + 1
           and emit zigzag = ()
           done
  and init dir = 1.0
  and init zeros = 0


(* open Dump *)
(* plot for [i=2:4] 'fly.out' using 1:i title column(i) with lines *)

open Scope

let hybrid main () =
  let der t = 1.0 init 0.0 in
  let (car1, car2, fly, zigzag, zeros) = model () in
  present (init) | up(t -. 2.0) | zigzag () ->
      let s = scope3 (-1.0, 100.0, ("car1", linear, car1),
                                   ("fly", linear, fly),
                                   ("car2", linear, car2))
      in print_int(zeros); print_newline (); flush stdout;
         window ("fly", 2.0, t, s)
  else ()

