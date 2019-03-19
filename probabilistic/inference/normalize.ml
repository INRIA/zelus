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

(** [normalize values] creates a distribution corresponding to the
    array of values [values]. *)
let normalize values =
  let norm = float (Array.length values) in
  let return_histogram = histogram_of_array values in
  Distribution.Dist_support
    (List.map (fun (v, n) -> (v, float n /. norm)) return_histogram)

(** [resample scores]
*)
let resample (states, scores, values) =
  let size = Array.length states in
  let states_values = Array.make size (states.(0), values.(0)) in
  let probabilities = Array.create_float size in
  let norm =
    let sum = ref 0. in
    Array.iteri
      (fun i score ->
         let w = max (exp score) epsilon_float in
         probabilities.(i) <- w;
         states_values.(i) <- (states.(i), values.(i));
         sum := !sum +. w)
      scores;
    !sum
  in
  Array.iteri (fun i w -> probabilities.(i) <- w /. norm) probabilities;
  let dist = Distribution.alias_method_unsafe states_values probabilities in
  Array.iteri
    (fun i _ ->
       let state, value = Distribution.draw dist in
       states.(i) <- copy state;
       values.(i) <- value;
       scores.(i) <- 0.)
    states
