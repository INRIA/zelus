(** [copy v] creates a deep copy of the value [v]. *)
let copy : 'a. 'a -> 'a =
  fun x -> Marshal.from_bytes (Marshal.to_bytes x [Marshal.Closures]) 0


(** [histogram_of_array l] create a histogram from an array of values. *)
let histogram_of_array l =
  let tbl = Hashtbl.create 7 in
  Array.iter
    (fun x ->
       try
         let n = Hashtbl.find tbl x in
         Hashtbl.replace tbl x (n + 1)
       with Not_found -> Hashtbl.add tbl x 1)
    l;
  Hashtbl.fold (fun x n acc -> (x, n)::acc) tbl []

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
  let support =
    List.sort (fun (_, x) (_, y) -> compare y x)
      (List.rev_map (fun (b, w) -> (b, w /. norm)) weights)
  in
  (* let dist = Distribution.Dist_support support in *)
  let dist = Distribution.alias_method support in
  Array.iteri
    (fun i _ ->
       let state, value = copy (Distribution.draw dist) in
       states.(i) <- state;
       values.(i) <- value;
       scores.(i) <- 0.)
    states
