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
