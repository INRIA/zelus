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

(** {2 Type definitions} *)

(** Probabilities (must be in the interval [0, 1]). *)
type proba = float

(** Logarithm of probabilities *)
type log_proba = float

(** Type of distributions *)
type 'a t =
  | Dist_sampler of ((unit -> 'a) * ('a -> log_proba))
  | Dist_support of ('a * proba) list

(** {2 Draw and score}*)

(** [draw dist] draws a value form the distribution [dist] *)
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

(** [score dist x] returns the log probability of the value [x] in the
    distribution [dist].
*)
let score dist x =
  begin match dist with
    | Dist_sampler (_, scorer) -> scorer x
    | Dist_support sup ->
      log (try List.assoc x sup
           with Not_found -> 0.)
  end

(** [draw dist] draws a value form the distribution [dist] and returns
    its log probability.
*)
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


(** {2 Opreations on distributions} *)

(** [multivariate dists] builds a multivariate distribution from a
    list of distributions.
*)
let multivariate dists =
  Dist_sampler
    ((fun () -> List.map (fun dist -> draw dist) dists),
     (fun xs ->
        List.fold_left2
          (fun acc dist x -> acc +. ((score dist) x))
          1.0
          dists xs))


(** [split dist] turns a distribution of pairs into a pair of
    distributions.
*)
let split dist =
  begin match dist with
  | Dist_sampler (draw, score) ->
      Dist_sampler ((fun () -> fst (draw ())), (fun _ -> assert false)),
      Dist_sampler ((fun () -> snd (draw ())), (fun _ -> assert false))
  | Dist_support support ->
      let s1, s2 =
        List.fold_right
          (fun ((a, b), p) (acc1, acc2) ->
             let add_p o =
               begin match o with
               | None -> p
               | Some p' -> p +. p'
               end
             in
             (Misc_lib.list_replace_assoc a add_p acc1,
              Misc_lib.list_replace_assoc b add_p acc2))
          support
          ([], [])
      in
      (Dist_support s1, Dist_support s2)
  end

(** [split_array dist] turns a distribution of arrays into an array of
    distributions.
*)
let split_array dist =
  begin match dist with
  | Dist_sampler (draw, score) ->
      (* We assume that all arrays in the distribution have the same length. *)
      let len = Array.length (draw ()) in
      Array.init len
        (fun i ->
           let draw () = (draw ()).(i) in
           let score _ = assert false in
           Dist_sampler (draw, score))
  | Dist_support [] -> Array.make 0 (Dist_support [])
  | Dist_support (((a0, p) :: _) as support) ->
      let supports =
        Array.make (Array.length a0) []
      in
      List.iter
        (fun (a, p) ->
           let add_p o =
             begin match o with
               | None -> p
               | Some p' -> p +. p'
             end
           in
           Array.iteri
             (fun i v ->
                supports.(i) <-
                  Misc_lib.list_replace_assoc v add_p supports.(i))
             a)
        support;
      Array.map (fun supp -> Dist_support supp) supports
  end


(** [split_list dist] turns a distribution of lists into a list of
    distributions.
*)
let split_list dist =
  begin match dist with
  | Dist_sampler (draw, score) ->
      assert false (* XXX TODO XXX *)
  | Dist_support [] -> []
  | Dist_support sup ->
      let rec map2' f1 f2 f12 l1 l2 =
        begin match l1, l2 with
        | l1, [] -> List.map f1 l1
        | [], l2 -> List.map f2 l2
        | x1::l1, x2::l2 -> f12 x1 x2 :: (map2' f1 f2 f12 l1 l2)
        end
      in
      let split =
        List.fold_left
          (fun accs (l, w) ->
             map2'
               (fun acc -> acc)
               (fun v -> [(v, w)])
               (fun acc v -> (v, w)::acc)
               accs l)
          [] sup
      in
      List.map (fun l -> Dist_support l) split
  end

(** [stats_float d] computes the mean and stddev of a [float
    Distribution.t].
*)
let stats_float d =
  match d with
  | Dist_sampler _ ->
    let rec stats n sum sq_sum =
      begin match n with
      | 100000 ->
	let mean = sum /. (float n) in
	let stddev = sqrt (sq_sum /. (float n) -. mean *. mean) in
	mean, stddev
      | _ ->
	let x = draw d in
	stats (n+1) (sum +. x) (sq_sum +. x*.x)
      end
    in stats 0 0. 0.
  | Dist_support sup ->
    let rec stats sup sum sq_sum =
      begin match sup with
      | [] ->
	let mean = sum in
	let stddev = sqrt (sq_sum -. mean *. mean) in
	mean, stddev
      | (v,w) :: t ->
	stats t (sum +. v *. w) (sq_sum +. w *. v *. v)
      end
    in stats sup 0. 0.



(** [mean_float d] computes the mean of a [float Distribution.t]. *)
let mean_float d =
  match d with
  | Dist_sampler _ ->
    let n = 100000 in
    let acc = ref 0. in
    for i = 1 to n do acc := !acc +. draw d done;
    !acc /. (float n)
  | Dist_support sup ->
    List.fold_left (fun acc (v, w) -> acc +. v *. w) 0. sup


(** [stats_float_list d] computes the mean and stddev of a
    [float list Distribution.t].
*)
let stats_float_list d =
  let ls = split_list d in
  List.map (fun l -> stats_float l) ls

(** [mean_float_list d] computes the means of a [float list Distribution.t]. *)
let mean_float_list d =
  let ls = split_list d in
  List.map (fun l -> mean_float l) ls


(** {2 Distributions} *)

(** [bernoulli theta] is a bernoulli distribution of parameter theta.
    @see<https://en.wikipedia.org/wiki/Bernoulli_distribution>
 *)
let bernoulli p =
  assert (0. <= p && p <= 1.);
  Dist_support [
    (true, p);
    (false, 1. -. p);
  ]


(** [gaussian mu sigma] is a normal distribution of mean [mu] and
    standard deviation [sigma].
    @see<https://en.wikipedia.org/wiki/Normal_distribution>
*)
let gaussian mu sigma =
  let two_pi = 2.0 *. 3.14159265358979323846 in
  let sigma2 = sigma ** 2. in
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
        -. 0.5 *. log (two_pi *. sigma2) -.
        (x -. mu) ** 2. /. (2. *. sigma2)))


(** [beta a b] is a beta distribution of parameters [a] and [b].
    @see<https://en.wikipedia.org/wiki/Beta_distribution>
 *)
let beta =
  let rec exp_gamma_sample shape scale =
    if (shape < 1.) then
     let r =
       exp_gamma_sample (1. +. shape) scale +. log (Random.float 1.) /. shape
     in
     if r = neg_infinity then
       (* log gamma sample underflow, rounded to nearest representable
          support value *)
       min_float
     else
       r
    else
      let d = shape -. 1. /. 3. in
      let c = 1. /. sqrt (9. *. d) in
      let rec loop () =
        let x = ref (draw (gaussian 0. 1.)) in
        let v = ref (1. +. c *. !x) in
        while !v <= 0. do
          x := draw (gaussian 0. 1.);
          v := 1. +. c *. !x;
        done;
        let log_v = 3. *. log !v in
        v := !v *. !v *. !v;
        let u = Random.float 1. in
        if ((u < 1. -. 0.331 *. !x *. !x *. !x *. !x)
            || (log u < 0.5 *. !x *. !x +. d *. (1. -. !v +. log !v))) then
          log scale +. log d +. log_v
        else
          loop ()
      in
      loop ()
  in
  let log_gamma x = assert false (* XXX TODO XXX *) in
  let log_beta a b =
    log_gamma a +. log_gamma b -. log_gamma (a +. b)
  in
  fun a b ->
    assert (a > 0.);
    assert (b > 0.);
    let draw () =
      let log_x = exp_gamma_sample a 1. in
      let log_y = exp_gamma_sample b 1. in
      let v = 1. /. (1. +. exp (log_y -. log_x)) in
      if v = 0. then
        (* beta sample underflow, rounded to nearest representable
           support value *)
        min_float
      else if v = 1. then
        (* beta sample overflow, rounded to nearest representable
           support value *)
        1. -. epsilon_float /. 2.
      else v
    in
    let score x =
    if x > 0. && x < 1. then
      (a -. 1.) *. log x +. (b -. 1.) *. log (1. -. x) -. log_beta a b
    else
        neg_infinity
    in
    Dist_sampler (draw, score)

(** [sph_gaussian mus sigmas] is a multivariate normal distribution.
    @see<https://en.wikipedia.org/wiki/Multivariate_normal_distribution>
*)
let sph_gaussian mus sigmas =
  multivariate (List.map2 gaussian mus sigmas)


(** [uniform_int low up] is a uniform distribution over integers
    between [low] and [up] included.
    @see<https://en.wikipedia.org/wiki/Discrete_uniform_distribution>
*)
let uniform_int low up =
  let draw () =
    Random.int (up - low + 1) + low
  in
  let score n =
    -. log (float (up - low))
  in
  Dist_sampler (draw, score)

(** [uniform_float low up] is a uniform distribution over floating
    points number between [low] and [up] included.
    @see<https://en.wikipedia.org/wiki/Uniform_distribution_(continuous)>
*)
let uniform_float low up =
  let draw () =
      Random.float (up -. low) +. low
  in
  let score n =
    -. log (up -. low)
  in
  Dist_sampler (draw, score)


(** [uniform_list l] is a categorical distribution where each element
    is equiprobable.
    @see<https://en.wikipedia.org/wiki/Categorical_distribution>
*)
let uniform_list l =
  let p = 1. /. float (List.length l) in
  Dist_support (List.map (fun x -> (x, p)) l)


(** [weighted_list l] is a categorical distribution where each element
    (x_i, w_i) has the probability w_i / (sum_i w_i)
 *)
let weighted_list l =
  let n = List.fold_left (fun n (w, x) -> n +. w) 0. l in
  Dist_support (List.rev_map (fun (w, x) -> x, w /. n) l)


(** [exponential lambda] is an exponential distribution of parameter lambda.
    @see<https://en.wikipedia.org/wiki/Exponential_distribution>
 *)
let exponential lambda =
  assert (lambda > 0.);
  let draw () =
    let u = Random.float 1. in
    -. log u /. lambda
  in
  let score x =
    if x >= 0. then log lambda -. lambda *. x
    else neg_infinity
  in
  Dist_sampler (draw, score)


(** [alias_method_unsafe values probabilities] is the [alias_method]
    where the arrays [values] and [probabilities] are not copied.
*)
let alias_method_unsafe values probabilities =
  let size = Array.length values in
  let size_f = float size in
  let probability = Array.create_float size in
  let alias = Array.make size 0 in
  let average = 1.0 /. size_f in
  let _, small, large =
    Array.fold_left
      (fun (i, small, large) p ->
         if p >= average then (i + 1, small, i :: large)
         else (i + 1, i :: small, large))
      (0, [], []) probabilities
  in
  let rec while_ small large =
    begin match small, large with
    | [], [] -> ()
    | less :: small, more :: large ->
        probability.(less) <- probabilities.(less) *. size_f;
        alias.(less) <- more;
        probabilities.(more) <-
          (probabilities.(more) +. probabilities.(less)) -. average;
        if (probabilities.(more) >= 1.0 /. size_f) then while_ small (more :: large)
        else while_ (more :: small) large
    | less :: small, [] ->
        probability.(less) <- 1.0;
        while_ small []
    | [], more :: large ->
        probability.(more) <- 1.0;
        while_ [] large
    end
  in
  while_ small large;
  let draw () =
    let column = Random.int size in
    let coin_toss = Random.float 1. < probability.(column) in
    if coin_toss then values.(column) else values.(alias.(column))
  in
  let score x =
    let exception Idx of int in
    try
      Array.iteri (fun i v -> if x = v then raise (Idx i)) values;
      log 0.
    with Idx i ->
      log (probabilities.(i))
  in
  Dist_sampler (draw, score)


(** [alias_method support] is the [alias_method] where [support] is a
    pair [(x, p)] of a value [x] of probability [p].
*)
let alias_method_list support =
  let size = List.length support in
  let values =
    begin match support with
    | [] -> assert false
    | (d, _) :: _ -> Array.make size d
    end
  in
  let probabilities = Array.create_float size in
  List.iteri (fun i (v, p) -> values.(i) <- v; probabilities.(i) <- p) support;
  alias_method_unsafe values probabilities

(** [alias_method values probabilities] is a discrete distribution where
    the value [value.(i)] has the probability [probabilities.(i)].
    @see<https://en.wikipedia.org/wiki/Alias_method>
*)
let alias_method values probabilities =
  let values = Array.copy values in
  let probabilities = Array.copy probabilities in
  alias_method_unsafe values probabilities
