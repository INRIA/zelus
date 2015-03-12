(*
  Use of a local continuous variable in the definition of another continuous
  variable.
 *)
let hybrid model () = x where
  rec
    init x = 0.0
  and
    automaton
    | S1 ->
        local y in
        do
          der y = 1.0 init 0.0
          and der x = y
        done

