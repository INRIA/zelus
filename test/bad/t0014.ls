
(* pour tester ../../compiler/hyc.byte -i -v -I ../../lib t15.ls *)
(* pour debugger
   set arguments -I ../lib ../test/good/t15.ls *)

type mode = M1 | M2

let hybrid main () =
  let rec
    der time = 1.0 init 0.0
  and
    mode = if time < 2.0 then M1 else M2
  and 
      init x = 0.0
  and
    match mode with
    | M1 ->
      let rec der y = 1.0 init 0.0 reset (up(x -. 1.0)) -> (2.0 *. last y) in
      do der x = y done
    | M2 ->
        let z = 1.0 +. x in
        do der x = 2.0 +. z done
    in
  x

