type ('s, 'a, 'b) muf_node =
    { init : 's;
      step : ('s * 'a -> 's * 'b); }

type ('s, 'a, 'b) instance =
    { state : 's;
      node : ('s, 'a, 'b) muf_node; }

let init node =
  let node = node () in
  { state = node.init;
    node = node; }

let step instance args =
  let state, o = instance.node.step (instance.state, args) in
  { instance with state = state}, o

let reset instance =
  { instance with state = instance.node.init }, ()

open Ztypes

type state

let cnode_of_muf_node node =
  let alloc () = ref (init node) in
  let step' state x =
    let instance, o = step !state x in
    state := instance;
    o
  in
  let reset state = state := fst (reset !state) in
  let copy src dst = dst := !src in
  Cnode { alloc; step = step'; reset; copy; }

let cnode_of_muf_proba_node node =
  let alloc () = ref (init node) in
  let step' state x =
    let instance, o = step !state x in
    state := instance;
    snd o
  in
  let reset state = state := fst (reset !state) in
  let copy src dst = dst := !src in
  Cnode { alloc; step = step'; reset; copy; }


let muf_node_of_cnode cnode () =
  let Cnode { alloc; step; reset; copy; } = cnode in
  let state = alloc () in
  let muf_step ((first, state), x) =
    if first then reset state;
    let o = step state x in
    (false, state), o
  in
  let (n : (bool * _, 'a, 'b) muf_node) =
    { init = (true, state); step =  muf_step; }
  in
  (Obj.magic n : (bool * state, 'a, 'b) muf_node)

let prob_op' n prob args =
  (prob, n (prob, args))

let prob_op pnode prob args =
  let Cnode { alloc; step; reset; copy; } = pnode in
  (prob, step (alloc()) (prob, args))
