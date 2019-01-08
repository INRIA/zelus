open Ztypes

type pstate = Infer.pstate

let sample = Infer.sample

let factor = Infer.factor

let infer n node =
  let Node { alloc; reset; step } = Infer.infer n node in
  Node { alloc = alloc;
         reset = reset;
         step = (fun state input -> step state (false, input)); }
