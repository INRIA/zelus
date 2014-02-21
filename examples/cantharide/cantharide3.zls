
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

let hybrid zigzagfly (car1, car2, fly) = (velocity, zig, zag) where
  rec automaton
      | TowardGirona -> do
            velocity = fly_velocity
          until up(fly -. car2) then do emit zag in TowardBarcelona

      | TowardBarcelona -> do
            velocity = -. fly_velocity
          until up(car1 -. fly) then do emit zig in TowardGirona

let hybrid model () =  (car1, car2, fly, zigzags) where
  rec der car1 = car_velocity init barcelona
  and der car2 = -. car_velocity init girona
  and der fly = fly_velocity init barcelona

  and automaton
      | Approaching -> do
            (fly_velocity, zig, zag) = zigzagfly(car1, car2, fly) 
          until up(car1 -. car2) then Receding
      | Receding -> do
            (* NB: arbitrary reset of the fly's direction to: TowardGirona *)
            (fly_velocity, zig, zag) = zigzagfly(car2, car1, fly) 
          done

  and zigzags = present
                | zig() -> last zigzags + 1
                | zag() -> last zigzags + 1
                init 0

  and _ = present
          | zig() -> print_status ("zig", car1, car2, fly, zigzags)
          | zag() -> print_status ("zag", car1, car2, fly, zigzags)

let hybrid main () = () where
  rec automaton
      | Running -> local car1, car2, fly, zigzags in do
            (car1, car2, fly, zigzags) = model ()
          until up(car1 -. girona) then
            do () = print_status ("done", car1, car2, fly, zigzags) in Finished
      | Finished -> do done

