(* HSCC Example 1 *)
let hybrid main () =
  let
  rec der x = 0.0 init -. 1.0
              reset
                (up(last y)   ) -> -. 1.0
              | (up(-. last y)) ->    1.0
              | (up(z)   ) ->    1.0

  and der y = 0.0 init -. 1.0
              reset
                (up(x)   ) ->    1.0
              | (up(-. x)) -> -. 1.0

  and der z = 1.0 init -. 1.0
  in
  ()

