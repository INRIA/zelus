let node switch i = o where
  automaton
  | False -> 
      do o = false until i then True
  | True -> 
      do o = true until i then False

let node switch_strong i = o where
  automaton
  | False ->
      do o = false unless i then True
  | True ->
      do o = true unless i then False

let node two i = o where
  rec automaton
      | Up ->
          do o = 0 -> pre o + 1 until (o = 5) continue Down
      | Down ->
          do o = 0 -> pre o - 1 until (o = -5) continue Up
  
let node main1 () =
  let i = read_int () in
  let i = not (i = 0) in
  let o = switch_strong i in
    if o then print_string "true" else print_string "false"; print_string " "

let node main2 () =
  let i1 = read_int () in
  let i = not (i1 = 0) in
  let o = two i in
  print_int o; print_string " "

let node main () = main1 ()

