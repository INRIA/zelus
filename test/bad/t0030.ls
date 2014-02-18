(* This program is rejected because z1 = y + 1 must be done before y = 1 *)
let node g(x) = 
  let rec init y = 0
  and match x with
      | 1 -> let z1 = y + 1 in do y = 1 done
      end in
  y
