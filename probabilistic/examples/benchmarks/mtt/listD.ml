open Ztypes

let map (Cnode { alloc; reset; copy; step; }) =
  let step state l =
    List.map (fun x -> step state x) l
  in
  Cnode { alloc; reset; copy; step; }
