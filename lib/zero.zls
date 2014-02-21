(* A library of zero-crossing functions *)
let hybrid orz(z1, z2) = present | z1 -> () | z2 -> ()

let hybrid upt(x) = up(if x > 0.0 then 1.0 else -1.0)

let hybrid upz(x) = z where
  automaton
  | Diff -> 
      let z = orz(init, up(x)) in
      do until z() on (x = 0.0) then Zero 
             | z() then Diff 
      done
  | Zero ->
      do until (orz(upt(x), upt(-. x)))() then do emit z = () in Diff done
  
