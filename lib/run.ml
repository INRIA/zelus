(* Higher-order operator to apply a stream of stream functions *)

open Ztypes

type 'a mem = { mutable m: 'a }

type 'a instance = I: { s : 's; t : 's -> 'a } -> 'a instance

(* [irun(f, x)] takes two streams [f : 'a -D-> 'b] and [x: 'a] *)
(* and computes [f(0)(x)] *)
let irun =
  let alloc () = { m = None } in
  let step self (f, x) =
    let I { s; t } =
      match self.m with
      | None ->
	 let Node { alloc; step; reset } = f in
	 let s = alloc () in
	 reset s;
	 let v = I { s = s; t = step } in
	 self.m <- Some(v); v
      | Some(s) -> s in
    t s x in
  let reset self = self.m <- None in
  Node { alloc = alloc; step = step; reset = reset }
