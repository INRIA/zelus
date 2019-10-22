open Ztypes

let map (Cnode { alloc; reset; copy; step; }) =
  let step state (pstate, l) =
    List.map (fun x -> step state (pstate, x)) l
  in
  Cnode { alloc; reset; copy; step; }


let ini (Cnode { alloc; reset; copy; step; }) =
  let step state (pstate, n) =
    List.init n (fun x -> step state (pstate, x))
  in
  Cnode { alloc; reset; copy; step; }


let filter (Cnode { alloc; reset; copy; step; }) =
  let step state (pstate, l) =
    List.filter (fun x -> step state (pstate, x)) l
  in
  Cnode { alloc; reset; copy; step; }


let iter2 (Cnode { alloc; reset; copy; step; }) =
  let step state (pstate, (l1, l2)) =
    List.iter2 (fun x y -> step state (pstate, (x, y))) l1 l2
  in
  Cnode { alloc; reset; copy; step; }
