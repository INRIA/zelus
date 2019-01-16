(** [copy v] creates a deep copy of the value [v]. *)
let copy : 'a. 'a -> 'a =
  fun x -> Marshal.from_bytes (Marshal.to_bytes x [Marshal.Closures]) 0

(** [normalize values] creates a distribution corresponding to the
    array of values [values]. *)
let normalize values =
  let norm = float (Array.length values) in
  let return_histogram =
    Array.fold_left
      (fun acc v ->
         Misc_lib.list_replace_assoc v
           (function None -> 1
                   | Some n -> n + 1)
           acc)
      [] values
  in
  Distribution.Dist_support
    (List.map (fun (v, n) -> (v, float n /. norm)) return_histogram)

(** [resample scores]
*)
let resample (states, scores, values) =
  let weights, norm =
    let sum = ref 0. in
    let acc = ref [] in
    Array.iteri
      (fun i score ->
         let w = max (exp score) epsilon_float in
         acc := ((states.(i), values.(i)), w) :: !acc;
         sum := !sum +. w)
      scores;
    (!acc, !sum)
  in
  let dist =
    Distribution.Dist_support
      (List.map (fun (b, w) -> (b, w /. norm)) weights)
  in
  Array.iteri
    (fun i _ ->
       let state, value = copy (Distribution.draw dist) in
       states.(i) <- state;
       values.(i) <- value;
       scores.(i) <- 0.)
    states
