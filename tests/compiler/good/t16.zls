
let node f x =
  let lx = pre(x) in
  let lx2 = lx + 2 in
  1 -> lx2

(*
let hybrid main m =
  let rec
      match m with
      | true -> local y in do der y = 1.0 done
      | false -> do done 
      in ()
*)

(*
type mode = M1 | M2
type submode = M2A | M2B

let hybrid main () =
  let rec
    der time = 1.0 init 0.0
  and
    mode = if time < 2.0 then M1 else M2
  and
    init x = 0.0 and init ll = 0.0
  and 
    match mode with
    | M1 ->
        local y in
        do der y = 1.0 init 0.0  reset (2.0 *. last y) every up(x -. 1.0)
        and der x = y and der ll = 0.5 done
    | M2 ->
      let z = 1.0 +. x in
      let submode = if time < 4.0 then M2A else M2B in
      do
        der x = 2.0 +. z
      and
        match submode with
        | M2A ->
            let rec der pq = 1.1 init 2.0
            and pr = (0 fby pr + 1) every up(pq) init 0 in
            do der ll = 2.0 done
        | M2B -> 
            do der ll = 1.0 done
      done
    in
  x
*)
