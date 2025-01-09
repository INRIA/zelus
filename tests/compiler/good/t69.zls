(* tester l'ajout du bit "goagain" *)
let hybrid f1 (x, y, k) = o where
  rec present
        x _ -> do reset o = 1 every k done
      | y _ -> do o = 2 done
      else do o = 3 done

(*
let hybrid g x = y where
  rec init y = 0.0 
  and present
      | x _ -> do y = last y +. 1.0 done
      else do der y = 2.0 done
*)

(*
let hybrid f (x, k) = o where
  rec match x with
      | true -> let rec der o1 = 1.0 init 2.0 in
                do o = o1 done
      | false -> do der o = 3.0 done
  and init o = 1.0 and o2 = 1.0
*)
(*let hybrid controller () = t1 where
  rec
      automaton
      | Nothing -> 
          let der t = 1.0 init last t1 in do t1 = t until z1 then Heat done
      | Heat -> 
          let der t = -1.0 init last t1 in do t1 = t until z2 then Nothing done
  and init t1 = 0.0
  and z1 = up(t1 -. 10.0) 
  and z2 = up(-. (t1 +. 10.0))
*)

(*
let hybrid main () =
   let o = controller () in
   let _ = (let _ = print_string "t = " in
            let _ = print_float o in
            print_newline ()) every (period (0.2)) default () in
   ()
*)

(*let hybrid g x = o where
  rec present
      | x(v) -> do emit o = v done
      else do emit o = 1 done *)

(*
let hybrid g () = z where
  rec match x with
      | true -> do der z = 1.0 done
      | false -> do der z = 2.0 done
  and init z = 0.0
  and x = not (last x) every period (1.0) init false
*)

(* let hybrid f x = o where
  rec der o = 1.0 +. x init 0.0

let hybrid g x = z where
  rec match x with
      | true -> do der z = 1.0 done
      | false -> do der z = 2.0 done
  and init z = 0.0
  and der k = 1.0 init 4.0
*)

(*
let node f () =
  let rec nat = 0 -> pre nat + 1 in
  nat + 1
     let x1, x2 = (1, 2) every true default 1,2 init 1, 2 in
  x1 *)
   
(*
let hybrid g () =
  let k1 = period (1.0) in
  (*let k2 = period (3.0) in*)
  k1
*)

(*
let hybrid g () =
  let o =
    (let rec der o1 = (let k = period (3.0) in
                       let rec der o2 = o2 +. 1.0 init 0.0 in o2) +. 1.0 init 0.0 in
    o1) +. 2.0 in
  let k2 = period (3.0) in
  let der o3 = 1.0 init 1.0 reset 0.1 every k2 in
  o +. o3
*)

(*
let hybrid f () =
  let rec der o1 = o1 +. 1.0 init 0.0 in
  let rec der o1 = 1.0 init 0.0 in
  let rec x = (last x) + 1 every s init 0
      and s = up(o1 +. 5.0) in
  ()
*)

(*
let hybrid f x = o where
  match true with
  | true ->
      let rec der o1 = 1.0 init 0.0
      (* and der l = o1 +. 2.0 init 3.0
      and s = up(l +. 5.0) *)
      and k = up(x +. 1.0) in
      do o = o1 +. 1.0 done
  | false ->
      let rec der r = 2.0 +. last r init 3.0 and k = up(r) in
      do o = 1.0 +. r done
*)

(*
let node count () =
  let rec x = 1.2 fby 1.3 fby 4.1 fby y
      and y = 3.1 fby 3.2 fby 0.1 fby y in
  x

let node main () =
  let x = count () in
  let rec cpt = x -> pre cpt +. x in
  print_float cpt;
  print_newline ()

let node f x = o1 where
  rec match x with
      | true -> do o1 = 1 done
  and init o1 = 0

let node g x = o1 where
  rec automaton
  | S1 -> do o1 = 1 and o2 = 2 until true then S2 done
  | S2 -> do match x with
             | true -> do o1 = last o1 + 1 done
             | false -> do o2 = 2 done
          done
*)

(*
let node count3 x = o where
  automaton
  | Zero -> do o = 0 until x then Plus(1) done
  | Plus(v) -> do o = v until x then Plus(v+1) done

let node h (x) = z + k where
  rec automaton
      | S1 -> do z = 1 unless x then S2 done
      | S2 -> do z = 1 -> last z + 1 unless x then S1 done
  and k = 1 -> last z + 1
*)

(*
let node f x =
  let rec nat = k1 + 1
  and init nat = 1
  and k1 = last nat + 1
  and k2 = 1 -> last k2 + 1
  and v = last nat 
  and r = last k2 in
  k2

let node g() =
  let rec nat = 0 -> pre nat + k
  and k = 2 -> pre k + pre nat + last k in
  nat + 1
*)

