(* pour tester ../../compiler/hyc.byte -i -v -I ../../lib t10.ls *)
(* pour debugger
   set arguments -I ../lib ../test/good/t10.ls *)

let node f2(x) =
  let rec nat = (0 fby nat) + 1 in
  let rec nat2 = nat + (0 fby nat2) + nat in
  nat + nat2

let node f3(r, x) =
  let rec
    nat = if r then 0 else pnat + 1
  and
    pnat = pre(nat) in
  let rec
    nat2 = nat + if r then 0 else pnat2 + nat
  and
    pnat2 = pre(nat2) in
  nat + nat2

type t = A1 | A2 | A3

let node h(x) = m + 1 where
  match x with
  | 1 -> do m = 2 done
  | 2 -> do m = 3 done

let node f(x) = y where
  rec
      automaton
      | S1 -> 
          let rec c = 0 -> pre c + last s' in
          do y = 1+c
          until true then do emit s = 2 and s' = 4 in S2
      | S2 -> 
          do y = 1 -> last y+2
          until (y = 10) then S1
  and init s' = 0

let node count(n, tick) = o where
  rec
    cpt = 0 -> (pre cpt + 1) mod n
  and
    o = false -> cpt = 0

let node mouse(click, top) =
  let rec
      automaton
      | Await -> do until click then One
      | One -> do until click then do emit double in Await
               else (count(4, top)) then do emit simple in Await
      end in
  (simple, double)


let node f(x) = y where
  rec
      automaton
      | S1 -> 
          let rec c = 0 -> pre c + 1 in
          do y = x 
          until true then S1
          else (y = 10) then S2(1)
          else (c = 10) then S1
      | S2(t) -> 
          do y = t + 1 - x and emit m = 1 
          until (y = -10) then S1
      end
  and
      cpt = 0 -> pre cpt + 1

let node f1(x) =
  let 
    match x with
    | true -> 
        local y in
        do _ = 0 -> pre y + 1
        and match true with true -> do y = 1 done | false -> do y = 2 done
        and (o, _) = (1,2) done
    | false -> 
        local z in local y in
        do z,y = 1, 2 and o = z done
    in o

let node f2(x) =
  let rec nat = 0 -> pre nat + 1 in
  let rec nat2 = nat + 0 -> pre nat2 + nat in
  nat + nat2

type t = A1 | A2 | A3

let node h(x) = m where
  match x with
  | 1 -> do m = 2 done
  | 2 -> do m = 3 done
 and
  init m = 1

let node count(n, tick) = o where
  rec
    cpt = 0 -> (pre cpt + 1) mod n
  and
    o = false -> cpt = 0

let node g(x) = 
  let rec
    match x with
    | A1 -> do y = 1 -> pre y + 1 done
    | A2 -> do y = 2 and emit z = y done
    in
  let
    present z(v) -> do o = y + v done in
  o

let node mouse(click, top) =
  let rec
      automaton
      | Await -> do until click then One
      | One -> local nb in
               do nb = count(4, top) 
               until click then do emit double in Await
               else (nb) then do emit simple in Await
      end in
  (simple, double)

