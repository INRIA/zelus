(* Original example: heating and cooling curve for h20 *)

(* Possible extensions:
   - add the effect of, and changes to, pressure
   - make the heat source variable (heating, then cooling)
   - heat an ice cube into steam, stop the heat, then add more ice
   - effect of mass changing
   - different material (e.g. iron)
   - more accurate models
   - etc., etc., etc.
 *)

(* [above (x) = true] when [x >= 0] *)
let hybrid above(x) = o where
  rec present up(x) | up(-. x) -> do o = not (last o) done
  and init o = (x >= 0.0)

let hybrid specific_heat_h20 x =
  if not (above(x)) then 2.11
  else if not (above (x -. 100.0)) then 4.1813
  else 2.080

let latent_heat_melting_h20     =  333.0  (* J/g *)
let latent_heat_evaporation_h20 = 2260.0 (* J/g *)

let melting_point_h20 = 0.0   (* C *)
let boiling_point_h20 = 100.0 (* C *)

let hybrid exceeds (value, upper) = up (value -. upper)
let hybrid recedes (value, lower) = up (lower -. value)

(* NB: using state patterns would make this more concise;
       or a composition of two automata communicating by signals? *)
let hybrid h20 (mass (* grams *), joules_per_sec) = temp where
  rec init temp = -. 50.0
  and automaton
      | Solid ->
          do
            der temp = joules_per_sec /. (mass *. specific_heat_h20 temp)
          until (exceeds (temp, melting_point_h20)) then Melting
      | Melting ->
          let der latent_heat = joules_per_sec init 0.0 in
          do
            der temp = 0.0
          until (exceeds (latent_heat, latent_heat_melting_h20 *. mass)) 
	  then Liquid
          else (recedes (latent_heat, 0.0)) then Solid 
                (* Is it possible to get stuck? *)
      | Freezing ->
          let der latent_heat = joules_per_sec init latent_heat_melting_h20 in
          do
            der temp = 0.0
          until (recedes (latent_heat, -. latent_heat_melting_h20 *. mass)) 
	  then Solid
	  else (exceeds (latent_heat, 0.0)) then Liquid
      | Liquid ->
          do
            der temp = joules_per_sec /. (mass *. specific_heat_h20 temp)
          until (exceeds (temp, boiling_point_h20)) then Vaporizing
          else (recedes (temp, melting_point_h20)) then Freezing
      | Vaporizing ->
          let der latent_heat = joules_per_sec init 0.0 in
          do
            der temp = 0.0
          until (exceeds (latent_heat, latent_heat_evaporation_h20 *. mass)) 
	  then Gas
          else (recedes (latent_heat, 0.0)) then Liquid 
                (* Is it possible to get stuck? *)
      | Condensing ->
          let der latent_heat = joules_per_sec init 0.0 in
          do
            der temp = 0.0
          until (recedes (latent_heat, -. latent_heat_evaporation_h20 *. mass))
	  then Liquid
          else (exceeds (latent_heat, 0.0)) then Gas 
                (* Is it possible to get stuck? *)
      | Gas ->
          do
            der temp = joules_per_sec /. (mass *. specific_heat_h20 temp)
          until (recedes (temp, boiling_point_h20)) then Condensing
      end

open Scope

let p = 10.0

let hybrid timer p = z where
  rec der t = 1.0 init 0.0 reset z -> 0.0 and z = up(last t -. p)

let hybrid main () =
  let temp = h20 (1000.0, 1400.0) in (* ~1L of water, 1400W *)
  let der t = 1.0 init 0.0 in
  present
  (timer p) ->
    let s1 = Scope.scope (-50.0, 150.0, ("h20 temp.", Scope.linear, temp))
    in Scope.window ("H2O", 2400.0, t, s1)
  else ()

