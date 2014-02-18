
let hybrid timer p = z where
  rec der t = 1.0 init -. p reset -. p every z
  and z = up(t)

let sign f = if abs_float f > f then -. 1.0 else 1.0

(* Doesn't work for negative numbers... *)
(* Needs underlying float_to_init for initialization... *)
let hybrid int_of_float f = i where
  rec i =   last i + 1 every up(f -. float (last i + 1))
          | last i - 1 every up(-. (f -. float (last i)))
          init truncate f

let node show_result (y, yi) =
  print_float y;
  print_string " ";
  print_int yi;
  print_newline ()

let hybrid main () = () where
  rec p = timer 0.05
  and der t = 1.0 init 0.0
  and der y = 10.0 *. cos t init 10.0 *. sin t
  and yi = int_of_float y
  and _ = show_result (y, yi) every p default () init ()

