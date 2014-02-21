let hybrid g(x) = z where
  rec init z = 0.0 
  and match x with 
      | true -> local y in
                do y = z and der z = y done
      end

let hybrid main () = x where
  rec init x = 0.0
  and automaton
      | S1 ->
          local y in
          do
            y = x and der x = y
          done
      end

(*
let node g(x) = y, k, m where rec
  automaton
  | S1 -> do y = 2 and m = 3 until x() then S1
  | S2 -> do y = 1 and m = 4 until k(w) then S1
  end
  and present x(_) -> do emit k = 0 done
*)

 (*let hybrid f1 x =
  let rec 
      automaton
      | S1 -> do der y = 1.0 until x then S2
      | S2 -> do done
      end
  and init y = 0.0 in
  y
*)

(*
let node h () = x where
  rec (x, _) = (1, 2) init (1, 2)
*)

(*
let node f(x) = o where 
  rec init o = 1 
  and reset
        match x with
        | true -> local o1 in
                  do o1 = 0 -> pre o1 + 1 and o = 1 + o1 done
        | false -> do o = 1 -> pre o done
        end
      every (last o) = 4
*)

(*
let node g(x) = o where
  rec o = 0 fby y and y = 2 fby o

let hybrid h(x) = o where
  rec o = present x -> last o + 1 init 0
*)

(*
let hybrid h(x) = 
  let der z = 1.0 init 0.0 in
  let o = present x -> (z +. 2.0) else 0.0 in
  o +. 2.0
*)

(*
let node h(x) = 
  let rec init y = 0 and init z = 2 and init k = 2 and init l = 2
  and present
      | true -> do y = 1 and z = l done
      end
  and present
      | true -> do k = y and l = 2 done
      end in
  y, z
*)

(*
let node g(x,z) = y, 1 where 
 rec y = x + 1 and x = 0 -> pre y + 1
*)

(*
let node h() = x where
  rec automaton
      | Init -> do x = 0 until (x >= 10) then Up done
      | Up -> do x = 0 until (x >= 20) then do emit y = x in Init done

let node f() = (x, y) where
  rec match true with
      | true -> do x = last y + 1 done
      | false -> do y = last x + 1 done
  and init x = 0
  and init y = 0
  and z = x + 1

let node g() = x where
  rec automaton
      | Init(x0) -> do x = x0 -> pre x + 1 until (x >= 10) then Up(x) done
      | Up(x0) -> do x = x0 -> pre x + 2 until (x >= 20) then Down done
      | Down -> do x = 0 then Init(0) done
      init Init(-1)

let node main() =
  let x = g() in
  print_int x; 
  print_newline ()
*)

(*
let hybrid f () = y where
  rec init y = 0.0
  and automaton
      | S1 -> 
	  local z in
          do der y = 1.0 reset z -> 10.0
          and z = up(y -. 10.0)
          until z then S2 done
      | S2 -> 
	  local z, y' in
          do y' = 1.0 and der y = y' and z = up(y -. 10.0)
          until z then S1 done

*)

(*
let hybrid f z = o where
  rec
      match z with
      | true -> present k -> do o = 1 done
      | false -> present r -> do o = 2 done
      end
*)
  
(* let hybrid g k =
  let m = f k in
  let v = exceed 1.0 in
  m +. 2.0 *)

(*
let node h x = x + 1

let hybrid g x = o where
  rec o = present x -> h 1 init 2

let hybrid f x = o where
  rec automaton
      | S1 -> 
	  do der o = 1.0 until x then do o = 2.0 in S1 done
  and init o = 0.0
*)

(*
let hybrid ff z = o where rec der o = 1.0 init 0.0 reset z -> 2.0

let hybrid g z = x where
  rec init x = 1.0
  and match z with 
      | true -> local y in do der y = 2.0 init 0.0 done 
      | false -> local z in do der z = 3.0 and init z = 2.3 done 

let node h () = () where
  rec x = 1 -> last x + 1

let hybrid main () = () where
  rec match true with
      | true -> do present (period 1.0 (2.0)) -> do done done
      | false -> do done

let node i(x) = () where
  rec
      match x with
      | true -> local m, last_m in
                do m = 1 -> last_m and last_m = pre(m) and r = m done
      | false -> do r = 2 done

let hybrid f1 (z, v) = c where
  rec der c = 1.0 init -. v reset z -> 2.0

let hybrid f2 (z, v) = c where
  rec present (z) -> do c = 2.0 done else do der c = 1.0 done
  and init c = -. v

let hybrid main2 () =
  let rec z = period(1.0)
      and c1 = f2(z, 1.0)
      and c2 = f2(z, 1.0) in
  c1 = c2

let hybrid f3(z) = o where
  rec present
         z -> do o = 1 done else do o = 2 done
*)
