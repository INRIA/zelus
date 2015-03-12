(* Fix step simulation with a Euler 0 method *)
(* Only used for debugging *)

(* Euler 0 *)
let euler f step n_lastx n_upz =
  let lastx = Array.make n_lastx 0.0 in
  let dx = Array.make n_lastx 0.0 in
  let pre_upz = Array.make n_upz 0.0 in
  let upz = Array.make n_upz 0.0 in
  let z = Array.make n_upz false in
  let ok = ref false in
  while true do
    f lastx dx upz z;
    ok := false;
    for i = 0 to n_upz do
      z.(i) <- (pre_upz.(i) < 0.0) && (upz.(i) >= 0.0);
      ok := !ok || z.(i);
      pre_upz.(i) <- upz.(i)
    done;
    if !ok then ()
    else
      for i = 0 to n_lastx do
        lastx.(i) <- lastx.(i) +. dx.(i) *. step
      done
  done
