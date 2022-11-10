(* The Zelus compiler, version 2.2-dev
  (2022-10-28-20:36) *)
open Ztypes
let vfi = 0.8

let dt = 0.1

let b = 0.136

let xl = 5.

type ('b , 'a) _exec =
  { mutable i_49 : 'b ; mutable m_45 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_49 = (false:bool) ; m_45 = ((42. , 42. , 42.):float * float * float) } in
  let exec_reset self  =
    (self.i_49 <- true:unit) in 
  let exec_step self () =
    (((if self.i_49 then self.m_45 <- (0. , vfi , 0.)) ;
      self.i_49 <- false ;
      (let ((x_46:float) , (x_47:float) , (x_48:float)) = self.m_45 in
       let (((xf_44:float) , (vf_43:float) , (af_42:float)): (float  *
                                                              float  * float)) =
           (x_46 , x_47 , x_48) in
       self.m_45 <- (((+.) xf_44 
                           (( *. ) (if (<) ((+.) vf_43  (( *. ) af_42  dt)) 
                                           0.
                                    then 0.
                                    else (+.) vf_43  (( *. ) af_42  dt))  
                                   dt)) ,
                     (if (<) ((+.) vf_43  (( *. ) af_42  dt))  0.
                      then 0.
                      else (+.) vf_43  (( *. ) af_42  dt)) ,
                     (if (>=) ((+.) ((+.) ((+.) ((+.) xf_44 
                                                      (( *. ) (if (<) 
                                                                    (
                                                                    (+.) 
                                                                    vf_43 
                                                                    (
                                                                    ( *. ) 
                                                                    af_42  dt))
                                                                     
                                                                    0.
                                                               then 0.
                                                               else
                                                                 (+.) 
                                                                   vf_43 
                                                                   (( *. ) 
                                                                    af_42  dt))
                                                               dt)) 
                                                ((/.) (( *. ) (if (<) 
                                                                    (
                                                                    (+.) 
                                                                    vf_43 
                                                                    (
                                                                    ( *. ) 
                                                                    af_42  dt))
                                                                     
                                                                    0.
                                                               then 0.
                                                               else
                                                                 (+.) 
                                                                   vf_43 
                                                                   (( *. ) 
                                                                    af_42  dt))
                                                              
                                                              (if (<) 
                                                                    (
                                                                    (+.) 
                                                                    vf_43 
                                                                    (
                                                                    ( *. ) 
                                                                    af_42  dt))
                                                                     
                                                                    0.
                                                               then 0.
                                                               else
                                                                 (+.) 
                                                                   vf_43 
                                                                   (( *. ) 
                                                                    af_42  dt)))
                                                       (( *. ) 2.  b))) 
                                          (( *. ) (if (<) ((+.) vf_43 
                                                                (( *. ) 
                                                                   af_42  dt))
                                                           0.
                                                   then 0.
                                                   else
                                                     (+.) vf_43 
                                                          (( *. ) af_42  dt))
                                                   dt)) 
                                    ((/.) (( *. ) (if (<) ((+.) vf_43 
                                                                (( *. ) 
                                                                   af_42  dt))
                                                           0.
                                                   then 0.
                                                   else
                                                     (+.) vf_43 
                                                          (( *. ) af_42  dt))
                                                   dt)  2.))  xl
                      then (~-.) b
                      else 0.)) ; (xf_44 , vf_43 , af_42))):float *
                                                            float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_51 : 'g ;
    mutable h_58 : 'f ;
    mutable i_56 : 'e ;
    mutable h_54 : 'd ;
    mutable result_53 : 'c ; mutable i_69 : 'b ; mutable m_65 : 'a }

let main (cstate_70:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_51 = false ;
      h_58 = 42. ;
      i_56 = (false:bool) ;
      h_54 = (42.:float) ;
      result_53 = (():unit) ;
      i_69 = (false:bool) ; m_65 = ((42. , 42. , 42.):float * float * float) } in
  let main_step self ((time_50:float) , ()) =
    ((self.major_51 <- cstate_70.major ;
      (let (result_75:unit) =
           let h_57 = ref (infinity:float) in
           (if self.i_56 then self.h_54 <- (+.) time_50  0.) ;
           (let (z_55:bool) = (&&) self.major_51  ((>=) time_50  self.h_54) in
            self.h_54 <- (if z_55 then (+.) self.h_54  dt else self.h_54) ;
            h_57 := min !h_57  self.h_54 ;
            self.h_58 <- !h_57 ;
            self.i_56 <- false ;
            (begin match z_55 with
                   | true ->
                       (if self.i_69 then self.m_65 <- (0. , vfi , 0.)) ;
                       self.i_69 <- false ;
                       (let ((x_66:float) , (x_67:float) , (x_68:float)) =
                            self.m_65 in
                        let (((xf_64:float) , (vf_63:float) , (af_62:float)): 
                            (float  * float  * float)) = (x_66 , x_67 , x_68) in
                        self.m_65 <- (((+.) xf_64 
                                            (( *. ) (if (<) ((+.) vf_63 
                                                                  (( *. ) 
                                                                    af_62  dt))
                                                             0.
                                                     then 0.
                                                     else
                                                       (+.) vf_63 
                                                            (( *. ) af_62  dt))
                                                     dt)) ,
                                      (if (<) ((+.) vf_63  (( *. ) af_62  dt))
                                               0.
                                       then 0.
                                       else (+.) vf_63  (( *. ) af_62  dt)) ,
                                      (if (>=) ((+.) ((+.) ((+.) ((+.) 
                                                                    xf_64 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    if 
                                                                    (<) 
                                                                    (
                                                                    (+.) 
                                                                    vf_63 
                                                                    (
                                                                    ( *. ) 
                                                                    af_62  dt))
                                                                     
                                                                    0.
                                                                    then 0.
                                                                    else
                                                                    (+.) 
                                                                    vf_63 
                                                                    (
                                                                    ( *. ) 
                                                                    af_62  dt))
                                                                     
                                                                    dt)) 
                                                                 ((/.) 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    if 
                                                                    (<) 
                                                                    (
                                                                    (+.) 
                                                                    vf_63 
                                                                    (
                                                                    ( *. ) 
                                                                    af_62  dt))
                                                                     
                                                                    0.
                                                                    then 0.
                                                                    else
                                                                    (+.) 
                                                                    vf_63 
                                                                    (
                                                                    ( *. ) 
                                                                    af_62  dt))
                                                                    
                                                                    (
                                                                    if 
                                                                    (<) 
                                                                    (
                                                                    (+.) 
                                                                    vf_63 
                                                                    (
                                                                    ( *. ) 
                                                                    af_62  dt))
                                                                     
                                                                    0.
                                                                    then 0.
                                                                    else
                                                                    (+.) 
                                                                    vf_63 
                                                                    (
                                                                    ( *. ) 
                                                                    af_62  dt)))
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    2.  b))) 
                                                           (( *. ) (if 
                                                                    (<) 
                                                                    (
                                                                    (+.) 
                                                                    vf_63 
                                                                    (
                                                                    ( *. ) 
                                                                    af_62  dt))
                                                                     
                                                                    0.
                                                                    then 0.
                                                                    else
                                                                    (+.) 
                                                                    vf_63 
                                                                    (
                                                                    ( *. ) 
                                                                    af_62  dt))
                                                                    dt)) 
                                                     ((/.) (( *. ) (if 
                                                                    (<) 
                                                                    (
                                                                    (+.) 
                                                                    vf_63 
                                                                    (
                                                                    ( *. ) 
                                                                    af_62  dt))
                                                                     
                                                                    0.
                                                                    then 0.
                                                                    else
                                                                    (+.) 
                                                                    vf_63 
                                                                    (
                                                                    ( *. ) 
                                                                    af_62  dt))
                                                                    dt)  
                                                           2.))  xl
                                       then (~-.) b
                                       else 0.)) ;
                        (let _ = print_float xf_64 in
                         self.result_53 <- print_newline ()))
                   | _ -> self.result_53 <- ()  end) ; self.result_53) in
       cstate_70.horizon <- min cstate_70.horizon  self.h_58 ; result_75)):
    unit) in 
  let main_reset self  =
    ((self.i_56 <- true ; self.i_69 <- true):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
