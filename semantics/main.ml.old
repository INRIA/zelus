(* The main evaluation function *)
open Monad
open Opt
open Value
open Coiteration
   
let n = 10

let from output (CoF { init ; step }) n =
  let rec fromrec s n =
    if n = 0 then return ()
    else
      let+ r, s = step s in
      let+ _ = output r in
      fromrec s (n-1) in
  fromrec init n
        
let program genv i_list e output =
  let i_list = Write.program i_list in
  let+ genv = Coiteration.program genv i_list in
  let+ cof = Coiteration.exp genv Env.empty e in
  from output cof n
