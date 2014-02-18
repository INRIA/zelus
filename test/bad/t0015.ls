(* pour tester ../../compiler/hyc.byte -i -v -I ../../lib t19.ls *)
(* pour debugger
   set arguments -I ../lib ../test/good/t19.ls *)

type mode = Apart | Together

let hybrid model () = y where
  rec
      init y = -.1.0
  and
      match mode with
      | Apart ->
          do
                der y = 1.0
            and present (up(y)) ->
                  do mode = Together done
          done
      | Together ->
          do
            der y = -1.0
          done
  and init mode = Apart

let hybrid main() =
  let y = model () in
  ()

