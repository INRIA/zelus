
let node count3 x = o where rec
  automaton
  | Zero -> do o = 0 until x then Plus(42)
  | Plus(v) ->
      local cpt in
      do o = v and cpt = 1 -> pre cpt + 1
      until 
        (o = 10) then Zero

let node main () =
  let rec x = true fby false fby false fby false fby x in
  let o = count3(x) in
  print_string (if x then "true" else "false");
  print_newline ();
  print_int o;
  print_newline ()
