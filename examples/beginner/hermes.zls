(* programmes du chapitre "Lucid Synchrone, un langage                     *)
(* de programmation des systemes reactifs", Paul Caspi, Gregoire Hamon     *)
(* et Marc Pouzet, Hermes International Publishing, Editeur Nicolas Navet, *)
(* ouvrage "Systemes Temps reel -- Volume 1, 2006" *)
(* adapte au cas 1er ordre *)

let xor (a, b) = (a & not(b)) or (not(a) & b)

let full_add (a, b, c) = (s, co) where
       s = xor (xor (a, b), c)
   and co = (a & b) or (b & c) or (a & c)

let half_add (a,b) = (s, co) 
  where s = xor (a, b) and co = a & b

let full_add2(a,b,c) = (s, co) where
  rec (s1, c1) = half_add(a,b)
  and (s, c2) = half_add(c, s1)
  and co = c2 or c1

let node edge c = false -> c & not (pre c)

let node count1 (d, t) = ok where
  rec ok = (cpt = d)
  and cpt = d -> if pre cpt = 1 then d
                 else if t then pre cpt - 1 else pre cpt

let node count10 t = count1 (10, t)

let node sum x = s where rec s = x -> pre s + x

let m1 = 100.0
let g1 = 9.81
let mg = m1 *. g1

let node integr1 (dt, x0, dx) = x where
  rec x = x0 -> pre x +. dx *. dt

type circle = { center: float * float; radius: float }

type color = Bleu | Rouge | Vert
type dir = Direct | Indirect | Indetermine | Immobile

let node direction i = d where
  rec pi = i fby i
  and ppi = i fby pi
  and match ppi, pi, i with
      | (Rouge, Rouge, Rouge) | (Bleu, Bleu, Bleu) 
      | (Vert, Vert, Vert) ->
            do d = Immobile done
      | (_, Bleu, Rouge) | (_, Rouge, Vert) | (_, Vert, Bleu) -> 
            do d = Direct done
      | (_, Rouge, Bleu) | (_, Bleu, Vert) | (_, Vert, Rouge) -> 
            do d = Indirect done
      | _ -> do d = Indetermine done

let node up_down (m, step) = o where
  rec match m with
      | true -> do o = last o + step done
      | false -> do o = last o - step done
  and init o = 0

let node up_down_with_last (m, step) = o where
  rec match m with
      | true -> do o = last_o + step done
      | false -> do o = last_o - step done
  and last_o = 0 -> pre o

let pres x = present x _ -> true else false

let node count2 x = cpt where
  rec cpt = if pres x then 1 -> pre cpt + 1 else 0 -> pre cpt

let node sum2 (x, y) = o where
  present
  | x(v) & y(w) -> do o = v + w done
  | x(v1) -> do o = v1 done
  | y(v2) -> do o = v2 done      
  else do o = 0 done

let node def (x, y) = o where 
  present 
  | x(v) -> do emit o = v done 
  | y(v) -> do emit o = v done

let node weak_switch on_off = o where
  automaton
  | Off -> do o = false until on_off then On
  | On -> do o = true until on_off then Off

let node strong_switch on_off = o where
  automaton
  | Off -> do o = false unless on_off then On
  | On -> do o = true unless on_off then Off

let node expect a = o where
  automaton
  | S1 -> do o = false unless a then S2
  | S2 -> do o = true done

let node abo (a, b) = (expect a) & (expect b)

let node abro (a, b, r) = o where
  reset
    o = abo(a, b)
  every r

let node alternate (d1, d2) = status where
  automaton
    True ->
      let rec c = 1 -> pre c + 1 in
      do status = true
      until (c = d1) then False
  | False ->
      let rec c = 1 -> pre c + 1 in
      do status = false
      until (c = d2) then True

let node up_down2 go = o where
  rec automaton
      | Init ->
           do o = 0 until go then Up
      | Up -> 
          do o = last o + 1
          until (o >= 5) then Down
      | Down -> 
          do o = last o - 1
          until (o <= - 5) then Up

let node adjust (p, m) = o where
  rec init o = 0
  and automaton
      | Idle ->
           do unless p then Incr
                else m then Decr
      | Incr ->
           do o = last o + 1 unless (not p) then Idle
      | Decr ->
           do o = last o - 1 unless (not m) then Idle

let node up_down3 () = o where
  rec automaton
      | Up -> do o = 0 -> last o + 1 until (o >= 5) continue Down
      | Down -> do o = last o - 1 until (o <= 5) continue Up

let node count3 x = o where
  automaton
  | Zero -> do o = 0 until x then Plus(1)
  | Plus(v) -> do o = v until x then Plus(v+1)

let node counting e = cpt where
  rec cpt = if e then 1 -> pre cpt + 1 else 0 -> pre cpt

let node switch (low, high) = o where
  rec automaton
      | Init -> do o = 0 then Up(1)
      | Up(u) ->
          do o = last o + u
          unless low(v) then Down(v)
      | Down(v) ->
          do o = last o - v
          unless high(w) then Up(w)

(* module Misc *)
let node integr (t, dx) = let rec x = 0.0 -> t *. dx +. pre x in x
let node deriv (t, x) = 0.0 -> (x -.(pre x))/. t

(* module Pendulum *)
let dt = 0.05 (* pas d'echantillonnage *)
let l = 10.0 (* longueur du pendule *)
let g = 9.81 (* acceleration *)

let node integr0 dx = integr(dt, dx)
let node deriv0 x = deriv(dt, x)

(* l'equation du pendule *)
let node equation (d2x0, d2y0) = theta where
  rec theta = integr0 (integr0 ((sin thetap) *. (d2y0 +. g)
                       -. (cos thetap) *. d2x0) /. l)
    and thetap = 0.0 fby theta

let node position (x0, y0) = 
    let d2x0 = deriv0 (deriv0 x0)  in
    let d2y0 = deriv0 (deriv0 y0)  in

    let theta = equation(d2x0, d2y0) in

    let x = x0 +. l *. (sin theta)  in
    let y = y0 +. l *. (cos theta)  in
    (x0, y0, x, y)

let low = 4
let high = 4
let delay_on = 5 (* en dixi\`emes de secondes *)
let delay_off = 1

let node count (d, t) = ok where
  rec ok = cpt = 1
  and cpt = d -> if t & not (pre ok) then pre cpt - 1 else pre cpt

let node edge1 x = false -> not (pre x) & x

let node heat (expected_temp, actual_temp) = on_heat where
  rec on_heat = if actual_temp <= expected_temp - low then true
                else if actual_temp >= expected_temp + high then false
                else false -> pre on_heat

let node heat1 (expected_temp, actual_temp) = on_heat where
  rec automaton
      | False -> 
          do on_heat = false 
          unless (actual_temp <= expected_temp - low) then True
      | True ->
          do on_heat = true 
          unless (actual_temp >= expected_temp + high) then False

let node command dsecond = (open_light, open_gas) where
  rec automaton
      | Open ->
          do open_light = true
          and open_gas = true
          until (count (delay_on, dsecond)) then Silent
      | Silent ->
          do open_light = false
          and open_gas = false
          until (count (delay_off, dsecond)) then Open

let node light (dsecond, on_heat, light_on) = 
                           (open_light, open_gas, nok) where
  rec automaton
      | Light_off ->
          do nok = false
          and open_light = false
          and open_gas = false
          until on_heat then Try
      | Light_on ->
          do nok = false
          and open_light = false
          and open_gas = true
          until (not on_heat) then Light_off
      | Try ->
          do
            (open_light, open_gas) = command dsecond
          until light_on then Light_on
           else (count (3, edge (not open_light))) then Failure
      | Failure ->
          do nok = true 
          and open_light = false
          and open_gas = false
          done

let node main1 (dsecond, res, expected_temp, actual_temp, light_on) =
                              (open_light, open_gas, ok, nok) where
  rec reset
            on_heat = heat (expected_temp, actual_temp)
        and (open_light, open_gas,nok) = light (dsecond, on_heat, light_on)
        and ok = not nok
      every res

let node main () = ()
