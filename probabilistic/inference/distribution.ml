(**********************************************************************)
(*                                                                    *)
(*                           ReactiveML                               *)
(*                    http://reactiveML.org                           *)
(*                    http://rml.inria.fr                             *)
(*                                                                    *)
(*                          Louis Mandel                              *)
(*                                                                    *)
(*  Copyright 2002, 2007 Louis Mandel.  All rights reserved.          *)
(*  This file is distributed under the terms of the GNU Library       *)
(*  General Public License, with the special exception on linking     *)
(*  described in file ../LICENSE.                                     *)
(*                                                                    *)
(*  ReactiveML has been done in the following labs:                   *)
(*  - theme SPI, Laboratoire d'Informatique de Paris 6 (2002-2005)    *)
(*  - Verimag, CNRS Grenoble (2005-2006)                              *)
(*  - projet Moscova, INRIA Rocquencourt (2006-2007)                  *)
(*                                                                    *)
(**********************************************************************)

type proba = float
type log_proba = float

type 'a t =
  | Dist_sampler of ((unit -> 'a) * ('a -> log_proba))
  | Dist_support of ('a * proba) list

let bernoulli p =
  assert (0. <= p && p <= 1.);
  Dist_support [
    (true, p);
    (false, 1. -. p);
  ]

let gaussian mu sigma =
  let two_pi = 2.0 *. 3.14159265358979323846 in
  let rec rand_pair () =
    let u1 = Random.float 1.0 in
    let u2 = Random.float 1.0 in
    if u1 < epsilon_float then rand_pair ()
    else u1, u2
  in
  Dist_sampler
    ((fun () ->
        let u1, u2 = rand_pair() in
        let z = sqrt (-.2. *. log u1) *. cos (two_pi *. u2) in
        z *. sigma +. mu),
     (fun x ->
        -. 0.5 *. log (two_pi *. sigma ** 2.) -.
        (x -. mu) ** 2. /. (2. *. sigma ** 2.)))

let draw dist =
  begin match dist with
    | Dist_sampler (sampler, _) -> sampler ()
    | Dist_support sup ->
      let sample = Random.float 1.0 in
      (* TODO data structure for more efficient sampling *)
      let rec draw sum r =
        begin match r with
          | [] -> assert false
          | (v, p) :: r ->
            let sum = sum +. p in
            if sample <= sum then v else draw sum r
        end
      in
      draw 0. sup
  end

let score dist x =
  begin match dist with
    | Dist_sampler (_, scorer) -> scorer x
    | Dist_support sup ->
      log (try List.assoc x sup
           with Not_found -> 0.)
  end

let draw_and_score dist =
  begin match dist with
    | Dist_sampler (sampler, scorer) ->
      let x = sampler () in
      x, (scorer x)
    | Dist_support sup ->
      let sample = Random.float 1.0 in
      (* TODO data structure for more efficient sampling *)
      let rec draw sum r =
        begin match r with
          | [] -> assert false
          | (v, p) :: r ->
            let sum = sum +. p in
            if sample <= sum then v, (log p) else draw sum r
        end
      in
      draw  0. sup
  end

let multivariate dists =
  Dist_sampler
    ((fun () -> List.map (fun dist -> draw dist) dists),
     (fun xs ->
        List.fold_left2
          (fun acc dist x -> acc +. ((score dist) x))
          1.0
          dists xs))

let sph_gaussian mus sigmas =
  multivariate (List.map2 gaussian mus sigmas)

let uniform_int low up =
  let draw () =
    Random.int (up - low + 1) + low
  in
  let score n =
    -. log (float (up - low))
  in
  Dist_sampler (draw, score)

let uniform_float low up =
  let draw () =
      Random.float (up -. low) +. low
  in
  let score n =
    -. log (up -. low)
  in
  Dist_sampler (draw, score)

let uniform_list l =
  let p = 1. /. float (List.length l) in
  Dist_support (List.map (fun x -> (x, p)) l)

let mean_float d =
  match d with
  | Dist_sampler _ ->
    let n = 100000 in
    let acc = ref 0. in
    for i = 1 to n do acc := !acc +. draw d done;
    !acc /. (float n)
  | Dist_support sup ->
    List.fold_left (fun acc (v, w) -> acc +. v *. w) 0. sup
