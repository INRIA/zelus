(* this program should be rejected because y and z are defined twice *)

let node f(x) = 
  let rec 
      automaton
      | A -> do y = 1 and z = 2 until true then A
      end
  and automaton
      | A -> do y = 1 and z = 2 until true then A
      end in
  y, z

let node g(x) = 
  let rec init y = 0 and init z = 2
  and match x with
      | true -> do y = 1 and z = 2 done
      end
  and match x with
      | true -> do y = 1 and z = 2 done
      end in
  y, z
