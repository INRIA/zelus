(** [copy v] creates a deep copy of the value [v]. *)
let copy : 'a. 'a -> 'a =
  fun x -> Marshal.from_bytes (Marshal.to_bytes x [Marshal.Closures]) 0

(** [histogram_of_array l] create a histogram from an array of values. *)
let histogram_of_array l =
  let tbl = Hashtbl.create 7 in
  Array.iter
    (fun x ->
       (* XXX TODO: look if we can share marshaling with copy XXX *)
       let k = Marshal.to_bytes x [Marshal.Closures] in
       try
         let (_, n) = Hashtbl.find tbl k in
         Hashtbl.replace tbl k (x, n + 1)
       with Not_found -> Hashtbl.add tbl k (x, 1))
    l;
  Hashtbl.fold (fun _ (x, n) acc -> (x, n)::acc) tbl []

(** [log_sum_exp scores] computes the logarithm of the sum of the
    exponentials of the arguments.:
    [log_sum_exp [| x1; ... xn|] = exp(x1) + ... + exp(xn)]
*)
let log_sum_exp scores =
  let max_score =
    Array.fold_right (fun s acc -> (max s acc)) scores neg_infinity
  in
  let sum_exp_scores =
    Array.fold_right
      (fun score acc -> exp (score -. max_score) +. acc)
      scores 0.0
  in
  max_score +. (log sum_exp_scores)

(** [normalize values] creates a distribution corresponding to the
    array of values [values]. *)
let normalize values =
  let norm = float (Array.length values) in
  let return_histogram = histogram_of_array values in
  Distribution.Dist_support
    (List.map (fun (v, n) -> (v, float n /. norm)) return_histogram)

let normalize_nohist values scores =
  let norm = log_sum_exp scores in
  let probabilities = Array.map (fun score -> exp (score -. norm)) scores in
  (probabilities,
   Distribution.Dist_support
     (Array.to_list (Array.map2 (fun value prob -> (value, prob)) values probabilities)))

(** [resample copy size probabilities states] resample the array of
    states [states] of length [size] according the probabilities distribution
    [probabilities]. The states are copied using the [copy] function.
 *)

let resample copy size probabilities states =
  let states_idx = Array.init size (fun i -> i) in
  let dist = Distribution.alias_method_unsafe states_idx probabilities in
  let mapping = Array.make size 0 in
  for _ = 1 to size do
    let i = Distribution.draw dist in
    mapping.(i) <- mapping.(i) + 1
  done;
  let _, to_remove, to_add =
    Array.fold_left
      (fun (i, to_remove, to_add) n ->
         begin match n with
         | 1 -> (i + 1, to_remove, to_add)
         | 0 ->
             begin match to_add with
             | [] -> (i + 1, i :: to_remove, to_add)
             | (j, 1) :: to_add ->
                 copy states.(j) states.(i);
                 (i + 1, to_remove, to_add)
             | (j, n) :: to_add ->
                 assert (n > 1);
                 copy states.(j) states.(i);
                 (i + 1, to_remove, (j, n - 1) :: to_add)
             end
         | n ->
             assert (n > 1);
             let rec fill n to_remove =
               begin match n, to_remove with
               | 0, _ -> (to_remove, to_add)
               | _, [] -> ([], (i, n) :: to_add)
               | _, j :: to_remove ->
                   copy states.(i) states.(j);
                   fill (n - 1) to_remove
               end
             in
             let to_remove, to_add = fill (n - 1) to_remove in
             (i + 1, to_remove, to_add)
         end)
      (0, [], []) mapping
  in
  assert (to_remove = [] && to_add = []);
  ()
