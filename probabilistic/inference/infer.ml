(* A zelus discrete node is implemented by a value of the following type *)
(* see module Ztypes *)
(* type ('a, 'b) node =
    Node: { alloc : unit -> 's;   (* 's is the internal state *)
            reset: 's -> unit;    (* initializes the state *)
            step: 's -> 'a -> 'b; (* the step function *)
          } -> ('a, 'b) node
*)

open Ztypes


let factor (f, f0) = f +. f0
let sample = Distribution.draw


let infer n (Node { alloc; reset; step }) =
    (* val infer :
         int -S-> (score * 'a -D-> score * 'b)
             -S-> bool * 'a -D-> 'b Distribution.t *)
    (* The infer function takes a number of particles, a node, and
       returns a node.  The node in argument takes as argument a score
       and an input and returns the updated score.  The node in output
       takes as argument a boolen indiacting to the instants to
       resample and the input and returns the infered output. *)
  let alloc () =
    Array.init n (fun _ -> alloc ()),
    Array.make n 0.0
  in
  let reset (states, scores) =
    Array.iter reset states;
    Array.fill scores 0 n 0.0
  in
  let step (states, scores) (c, input) =
    let values =
      Array.mapi
        (fun i state ->
          let score, value = step state (scores.(i), input) in
          scores.(i) <- score;
          value)
        states
    in
    if c then Normalize.resample (states, scores, values);
    Normalize.normalize values
  in
  Node { alloc = alloc; reset = reset; step = step }


(* [memoize f x] is functionally equivalent to [f x] but stores *)
(* all the pairs (state, input) and the associated result *)
let memoize_step step (s, table) x =
  try
    Hashtbl.find table (s, x)
  with
  | Not_found ->
      let sc = Normalize.copy s in
      let o = step s x in
      Hashtbl.add table (sc, x) o;
      o

let memoize (Node { alloc; reset; step }) =
  let alloc () =
    alloc (), Hashtbl.create 7
  in
  let reset (s, table) =
    reset s; Hashtbl.clear table
  in
  Node { alloc = alloc; reset = reset; step = memoize_step step }



let expectation scores =
  let s = Array.fold_left (+.) 0. scores in
  s /. float (Array.length scores)


let plan_step n k model_step =
  let table = Hashtbl.create 7 in
  let rec expected_utility (state, score) (ttl, input) =
    if ttl < 1 then score
    else
      let states = Array.init n (fun _ -> Normalize.copy state) in
      let scores = Array.make n 0.0 in
      let score' =
        Array.iteri
          (fun i state ->
            let score, _ = model_step state (scores.(i), input) in
            let eu =
              memoize_step
                expected_utility ((state, score), table) (ttl - 1, input)
            in
            scores.(i) <- eu)
          states;
        let scores' = Array.copy scores in
        Normalize.resample (states, scores, scores');
        expectation scores'
      in
      score +. score'
  in
  let step states scores input =
    let values =
      Array.mapi
        (fun i state ->
          let score, value = model_step state (scores.(i), input) in
          scores.(i) <- expected_utility (state, score) (k, input);
          value)
        states
    in
    let states_scores_values =
      Array.mapi (fun i state -> (state, scores.(i), values.(i))) states
    in
    Normalize.resample (states, scores, states_scores_values);
    Hashtbl.clear table;
    states_scores_values
  in
  step

(* [plan n k f x] runs n instances of [f] on the input stream *)
(* [x] but at each step, do a prediction of depth k *)
let plan n k (Node model : (float * 't1, float * 't2) Ztypes.node) =
  let alloc () = ref (model.alloc ()) in
  let reset state = model.reset !state in
  let step_XXXX = plan_step n k model.step in
  let step plan_state input =
    let states = Array.init n (fun _ -> Normalize.copy !plan_state) in
    let scores = Array.make n 0.0 in
    let states_scores_values = step_XXXX states scores input in
    let dist = Normalize.normalize states_scores_values in
    let state', _, value = Distribution.draw dist in
    plan_state := state';
    value
  in
  Node { alloc = alloc; reset = reset; step = step }


type 'state infd_state =
    { infd_states : 'state array;
      infd_scores : float array; }

let infer_depth n k (Node model) =
  let alloc () =
    { infd_states = Array.init n (fun _ -> model.alloc ());
      infd_scores = Array.make n 0.0; }
  in
  let reset state =
    Array.iter model.reset state.infd_states;
    Array.fill state.infd_scores 0 n 0.0
  in
  let step infd_state input =
    let states_scores_values =
      plan_step n k
        model.step infd_state.infd_states infd_state.infd_scores input
    in
    let values = Array.map (fun (_, _, v) -> v) states_scores_values in
    Normalize.normalize values
  in
  Node { alloc = alloc; reset = reset; step = step }


let () = Random.self_init ()
