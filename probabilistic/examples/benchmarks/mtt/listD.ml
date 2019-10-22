open Ztypes

let iter2_proba (Cnode { alloc; reset; copy; step; }) =
  let step state (pstate, (l1, l2)) =
    List.iter2 (fun x y -> step state (pstate, (x, y))) l1 l2
  in
  Cnode { alloc; reset; copy; step; }

let map (Cnode { alloc; reset; copy; step; }) =
  let step state l =
    List.map (fun x -> step state x) l
  in
  Cnode { alloc; reset; copy; step; }
