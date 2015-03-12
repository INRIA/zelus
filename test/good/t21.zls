

let node up_down () = o where
  rec automaton
      | Up ->
           let rec cpt = 0 -> pre cpt + 1 in
           do o = cpt until (o = 10) then Down
      | Down -> 
          let rec cpt = 0 -> pre cpt + 1 in
          do o = cpt
          until (o = 10) then Up 
  and init o = 0

let node main1 () =
  let o = up_down () in
  print_int o;
  print_newline ()

let hybrid f () = o where
  rec match true with
      | true -> do der o = 1.0 done
      | false -> do der o = 2.0 done
  and init o = 0.0

let hybrid f2 () = o where
  rec automaton
  | Up -> do der o = 1.0 until (up(o -. 10.0)) continue Down
  | Down -> do der o = -1.0 until (up(-. o +. 10.0)) continue Up
  and init o = 0.0

open Scope

let p = 0.1

let hybrid timer p = z where
  rec der t = 1.0 init 0.0 reset z -> 0.0 and z = up(last t -. p)

