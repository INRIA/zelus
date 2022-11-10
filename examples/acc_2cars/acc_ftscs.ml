(* The Zelus compiler, version 2.2-dev
  (2022-10-28-20:36) *)
open Ztypes
let vfi = 8.8

let dt = 0.1

let b = 0.136

let xl = 5.

type ('b , 'a) _exec =
  { mutable i_29 : 'b ; mutable m_25 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_29 = (false:bool) ; m_25 = ((42. , 42. , 42.):float * float * float) } in
  let exec_reset self  =
    (self.i_29 <- true:unit) in 
  let exec_step self () =
    (((if self.i_29 then self.m_25 <- (xl , vfi , 0.)) ;
      self.i_29 <- false ;
      (let ((x_26:float) , (x_27:float) , (x_28:float)) = self.m_25 in
       let (((df_21:float) , (vf_22:float) , (af_20:float)): (float  *
                                                              float  * float)) =
           (x_26 , x_27 , x_28) in
       let (v_next_23:float) =
           if (<) ((+.) vf_22  (( *. ) af_20  dt))  0.
           then 0.
           else (+.) vf_22  (( *. ) af_20  dt) in
       let (d_next_24:float) = (-.) df_21  (( *. ) v_next_23  dt) in
       self.m_25 <- (d_next_24 ,
                     v_next_23 ,
                     (if (<=) ((-.) ((-.) ((-.) d_next_24 
                                                ((/.) (( *. ) v_next_23 
                                                              v_next_23) 
                                                      (( *. ) 2.  b))) 
                                          (( *. ) v_next_23  dt)) 
                                    ((/.) (( *. ) v_next_23  dt)  2.))  
                              0.5
                      then (~-.) b
                      else 0.)) ; (df_21 , vf_22 , af_20))):float *
                                                            float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
