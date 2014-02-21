
let barcelona = 0.0
let girona = 100.0

let fly_velocity = 80.0
let car_velocity = 50.0

let node print_status (eventname, car1, car2, fly, zigzags ) =
  flush stdout;
  print_endline (eventname ^ ": car1=" ^ (string_of_float car1)
                   ^ "; car2=" ^ (string_of_float car2)
                   ^ "; fly="  ^ (string_of_float fly)
                   ^ "; zigzags=" ^ (string_of_float (float(zigzags) /. 2.0)))


let hybrid model () =  (car1, car2, fly, zeros) where
  rec der car1 = car_velocity init barcelona
  and der car2 = -. car_velocity init girona
  and der fly = dir *. fly_velocity init barcelona
  and present 
        up (car1 -. fly)| up(car2 -. fly) |
        up(fly -. car1) | up(fly -. car2) -> 
           do dir = -. (last dir)
           and zeros = last zeros + 1
           and emit zigzag = ()
           and () = print_status ("zigzag", car1, car2, fly, zeros)
           done
  and init dir = 1.0
  and init zeros = 0

let hybrid main () = () where
  rec automaton
      | Running -> local car1, car2, fly, zigzags in do
            (car1, car2, fly, zigzags) = model ()
          until up(car1 -. girona) then
            do _ = print_status ("done", car1, car2, fly, zigzags) in Finished
      | Finished -> do done

