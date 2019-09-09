open Ztypes
open Infer_pf

type pstate = Infer_pf.pstate

let sample = Infer_pf.sample
let factor = Infer_pf.factor
let observe = Infer_pf.observe


let infer_decay n decay (Cnode { alloc; reset; copy; step }) =
  let alloc () =
    { infer_states = Array.init n (fun _ -> alloc ());
      infer_scores = Array.make n 0.0; }
  in
  let reset state =
    Array.iter reset state.infer_states;
    Array.fill state.infer_scores 0 n 0.0
  in
  let step { infer_states = states; infer_scores = scores } input =
    let values =
      Array.mapi
        (fun i state ->
          let value = step state ({ idx = i; scores = scores; }, input) in
          value)
        states
    in
    let weights, norm =
      let sum = ref 0. in
      let acc = ref [] in
      Array.iteri
        (fun i score ->
          let w = max (exp score) epsilon_float in
          acc := (values.(i), w) :: !acc;
          sum := !sum +. w)
        scores;
      (!acc, !sum)
    in
    if decay <> 1. then
      Array.iteri (fun i score -> scores.(i) <- decay *. score) scores;
    Distribution.Dist_support
      (List.rev_map (fun (b, w) -> (b, w /. norm)) weights)
  in
  let copy src dst =
    for i = 0 to n - 1 do
      copy src.infer_states.(i) dst.infer_states.(i);
      dst.infer_scores.(i) <- src.infer_scores.(i)
    done
  in
  Cnode { alloc = alloc; reset = reset; copy = copy; step = step }


let infer n node =
  infer_decay n 1. node

