open Basics

(*
Relies on zero-crossing detection on a DISCONTINUOUS function during integration 

In this case exchanging positions on zero-crossing is not necessary
and even DANGEROUS since it results on a discrete zc that cannot be
seen by the solver !
N.B. with this solution, balls are always "moving a little" after the first
hit, resulting on "micro zc" beetween the two (seemingly) immobile balls 

N.B. Differs from cradle3 which relies on the new "discrete zero-crossing" feature
*)

let node sc6 (yl, yu,
        (n1, t1, v1), (n2, t2, v2),
        (n3, t3, v3),
        (n4, t4, v4),
        (n5, t5, v5),
        (n6, t6, v6)) =
  let
  rec s1 = (Gtkplot.signal (n1, t1)) fby s1
  and s2 = (Gtkplot.signal (n2, t2)) fby s2
  and s3 = (Gtkplot.signal (n3, t3)) fby s3
  and s4 = (Gtkplot.signal (n4, t4)) fby s4
  and s5 = (Gtkplot.signal (n5, t5)) fby s5
  and s6 = (Gtkplot.signal (n6, t6)) fby s6
  and sc = (Gtkplot.scope (yl, yu,
       cons (s1, (cons (s2, cons (s3, cons (s4, cons ( s5, singleton s6))))))))
           fby sc
  in
  Gtkplot.update (s1, v1);
  Gtkplot.update (s2, v2);
  Gtkplot.update (s3, v3);
  Gtkplot.update (s4, v4);
  Gtkplot.update (s5, v5);
  Gtkplot.update (s6, v6);
  sc

let pi = 3.1416
let mp6 = -. (pi /. 6.)
let g = 9.80665
let l = 0.2

(* let pinit0 = mp6  let pinit1 = 0.0  let pinit2 = 0.0 *)
let pinit0 = mp6  let pinit1 = 0.0  let pinit2 = -. mp6
(* let pinit0 = mp6  let pinit1 = mp6  let pinit2 = 0.0 *)

let acc x = -. g /. l *. (sin x)
let becomes x = if x then 1. else -.1.

(* Zero crossing detections with two modes. Detect first a crossing *)
(* then the instant where it unsticks from zero *)
let hybrid mup(x) = ok where
  automaton
  | Init ->
      do until (init on (x = 0.0)) then Zero | (init) then Await done
  | Await ->
      let o = up(x) in
      do until 
           | o on (x = 0.0) then do emit ok = () in Zero
           | o then do emit ok = () in Await done
  | Zero ->
      do until up(if x > 0.0 then 1.0 else -1.0) then do emit ok = () in Await done

(* let ground x = World.ground(x) *)

(* Main entry point *)
let hybrid cradle () = (p0, p1 +. 1.0 , p2 +. 2.0 , h1, h2) where 
  (* three automata *)
  rec init p1 = pinit1
  and init v1 = 0.0
  and init v1_for_0 = 0.0
  and init v1_for_2 = 0.0
  and automaton
  | Running ->
      do der p1 = v1
      and der v1 = acc(p1)
      until
      | hit01() & hit12() then
          do v1_for_2 = last v0 and v1_for_0 = last v2 in NoRead 
      | hit01() then do v1_for_0 = last v1 in ReadLeft
      | hit12() then do v1_for_2 = last v1 in ReadRight
      done
  | NoRead -> do until (init) then Running done
  | ReadLeft ->
      do until (init) then 
          do v1 = last v0_for_1 
          and p1 = if last v1 = 0.0 then last p1 else last p0 
          in Running done
  | ReadRight ->
      do until (init) then 
          do v1 = last v2_for_1 
          and p1 = if last v1 = 0.0 then last p1 else last p2 
          in Running done
  and hit01 = mup(last p0 -. last p1)
  and hit12 = mup(last p1 -. last p2)

  and init p0 = pinit0
  and init v0 = 0.0
  and init v0_for_1 = 0.0
  and automaton
  | Running ->
      do der p0 = v0
      and der v0 = acc(p0)
      until hit01() then do v0_for_1 = last v0 in Read
      done
  | Read ->
      do until (init) then 
          do v0 = last v1_for_0 
          and p0 = if last v0 = 0.0 then last p0 else last p1 
          in Running done

  and init p2 = pinit2
  and init v2 = 0.0
  and init v2_for_1 = 0.0
  and automaton
  | Running ->
      do der p2 = v2
      and der v2 = acc(p2)
      until hit12() then do v2_for_1 = last v2 in Read
      done
  | Read ->
      do until (init) then 
           do v2 = last v1_for_2 
           and p2 = if last v2 = 0.0 then last p2 else last p1 
           in Running done
  
  (* and h1 = present hit01 -> -1.0 *. last h1 init -0.1
  and h2 = present hit12 -> -1.0 *. last h2 init -0.1 *)

  and h1 = v1_for_2
  and h2 = v2_for_1


let hybrid cradle_old () =
  let
  rec der p0 = v0 init pinit0
  and der v0 = acc (p0) init 0.0
  and der p1 = v1 init pinit1
  and der p2 = v2 init pinit2
  and der v1 = acc (p1) init 0.0
  and der v2 = acc (p2) init 0.0
  and present
  | hit01 & hit12 ->
    do
      v2 = last v0 and v0 = last v2
      and p0 = if last v0 = 0.0 then last p0 else
        if last v1 = 0.0 then last p1 else last p2
      and p1 = if last v1 = 0.0 then last p1 else
        if last v0 = 0.0 then last p0 else last p2
      and p2 = if last v2 = 0.0 then last p2 else
        if last v0 = 0.0 then last p0 else last p1
    done

  | hit01 ->
    do
      v1 = last v0 and v0 = last v1
      (* forcer des positions propres pour garantir l'immobilité parfaite *)
      (* and p0 = if last v0 = 0.0 then last p0 else last p1 *)
      (* and p1 = if last v1 = 0.0 then last p1 else last p0 *)
      and p0 = if last v0 = 0.0 then last p0 else
        if last v1 = 0.0 then last p1 else last p2
      and p1 = if last v1 = 0.0 then last p1 else
        if last v0 = 0.0 then last p0 else last p2
      and p2 = if last v2 = 0.0 then last p2 else
        if last v0 = 0.0 then last p0 else last p1
    done

  | hit12 ->
    do
      v2 = last v1 and v1 = last v2
      (* forcer des positions propres pour garantir l'immobilité parfaite *)
      (* and p1 = if last v1 = 0.0 then last p1 else last p2 *)
      (* and p2 = if last v2 = 0.0 then last p2 else last p1 *)
      and p0 = if last v0 = 0.0 then last p0 else
        if last v1 = 0.0 then last p1 else last p2
      and p1 = if last v1 = 0.0 then last p1 else
        if last v0 = 0.0 then last p0 else last p2
      and p2 = if last v2 = 0.0 then last p2 else
        if last v0 = 0.0 then last p0 else last p1
    done
  and hit01 = up (becomes (last p0 > last p1))
  and hit12 = up (becomes (last p1 > last p2))

  and h1 = present hit01 -> -1.0 *. last h1 init -0.1
  and h2 = present hit12 -> -1.0 *. last h2 init -0.1

  in p0, p1 +. 1.0 , p2 +. 2.0 , h1, h2 


let hybrid main () =
  let der t = 1.0 init 0.0 in
  let p0, p1, p2, h1, h2 = cradle () in
  present (period (0.02)) ->
      let s = sc6 (-1.0, 3.0,
         ("p0", Scope.linear, p0),
         ("h1,", Scope.linear, h1 +. 0.5),
         ("p1", Scope.linear, p1),
         ("h2,", Scope.linear, h2 +. 1.5),
         ("p2", Scope.linear, p2),
         ("", Scope.linear, -0.6)
   )
      in Scope.window ("cradle_modular", 3.0, t, s)

  else ()
