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

let muf_node znode =
  let Node { alloc; step; reset } = znode in
  let state = alloc () in
  let muf_step ((first, state), x) =
    if first then reset state;
    let o = step state x in
    (false, state), o
  in
  let n = { init = (true, state); step =  muf_step; } in
  (Obj.magic n : (bool * state, 'a, 'b) muf_node)
