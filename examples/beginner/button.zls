(* simple automata *)
type button = Up | Down

(* producing events from the keyboard *)
let node event key = button where
  match key with
  | "P" -> do emit button = Up done
  | "M" -> do emit button = Down done
  | _ -> do done

(* transforming a double button into an integer value *)
let node button_to_integer (i, step, button) = o where
  rec init o = i
  and present
        button(v) ->
          do match v with
             | Up -> do o = last o + step done
             | Down -> do o = last o - step done
          done

(* printing things *)
let node print_button b =
  match b with
  | Up -> print_string "Up"
  | Down -> print_string "Down"

(* simple two mode automaton *)
let node two_mode b = o where
  rec init o = 0
  and automaton
      | One ->
        let rec nat = 0 -> pre nat + 1 in
        do o = last o + nat until b then Two
      | Two ->
        do o = last o - 1 until b then One

let node main () =
  let key = read_int () in
  let b = if key = 0 then false else true in
  let o = two_mode b in
    print_int o;
    print_string " ";
    flush stdout

let node input1 () =
  let key = read_line () in
  let i = event key in
  let o = button_to_integer(20, 1, i) in
  print_int o;
  print_string " "

let node print i =
  present
  | i(b) -> print_button b
  else ()
 
 let node input () =
  let key = read_line () in
  let i = event key in
  print i

