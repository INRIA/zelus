let i1 j = k where
  match true with
  | true -> do match true with
            | true -> do emit k = () done
	    | false -> do done
         done
  | false -> do done

let hybrid f (x) =
  let rec der m = 1.0 init 0.0 in
  m +. x +. 1.0

let hybrid g(x) =
  let rec der m = 1.0 +. 2.0 init 0.0 
  and der z = m init 1.0 and k = z and l = up(m) in
  m

let hybrid h(x, y) =
  let z = x+1 in
  let t = y+1 in
  z, t

let hybrid main () =
  let _ = f(3.0)
  and _ = g(4.0) in
  let _ = f(3.0)
  and _ = g(4.0) in
  let _ = f(3.0)
  and _ = g(4.0) in
  let _ = f(3.0)
  and _ = g(4.0) in
  ()

