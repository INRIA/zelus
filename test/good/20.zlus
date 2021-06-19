
let hybrid model () = y where
  rec
      der x = 2.0 init 0.0
  and
      automaton
      | Apart ->
          do
            y = 1.0
          until (up(x -. 2.0)) then Together
      | Together ->
          do
            y = 2.0
          until (up(x -. 5.0)) then Apart

let hybrid main() =
  let y = model () in
  ()

