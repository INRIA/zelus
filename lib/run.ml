(* Higher-order operator to apply a stream of stream function *)

type 'a mem = { mutable m: 'a }

type 'a instance = I: { s : 's; t : 's -> 'a } -> 'a instance

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
