open Ztypes
type t = Zero | Constant of float | Linear of float 
type ('a) _simpl_chunk =
  { mutable result_25 : 'a }

let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
let simpl_chunk  = 
  
  let simpl_chunk_alloc _ =
    ();{ result_25 = (None:('b * t) Stdlib.option) } in
  let simpl_chunk_reset self  =
    ((()):unit) in 
  let simpl_chunk_step self ((dur_23:'a112) , (typ_24:t)) =
    (((begin match typ_24 with
             | Zero -> self.result_25 <- None
             | Constant((v_26:float)) ->
                 let (new_c_28:t) = Zero in
                 self.result_25 <- Some((dur_23 , new_c_28))
             | Linear((v_29:float)) ->
                 let (new_c_31:t) = Constant(v_29) in
                 self.result_25 <- Some((dur_23 , new_c_31))
              end) ; self.result_25):('b * t) Stdlib.option) in
  Node { alloc = simpl_chunk_alloc; reset = simpl_chunk_reset ;
                                    step = simpl_chunk_step }
