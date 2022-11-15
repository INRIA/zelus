(* The Zelus compiler, version 2.2-dev
  (2022-11-10-21:54) *)
open Ztypes

   external robot_get: string -> float = "robot_get_cpp" 

   external robot_str_ml: string -> float -> unit = "robot_str_cpp" 

   external lcm_start: unit -> int = "LCM_start" 
 
   external lcm_stop: unit -> unit = "LCM_stop" 

  
 let () = ignore(lcm_start())
let vfi = 0.5

let dt = 0.1

let b = 0.136

let xli = 2.

let xbrake = 4.

let amax = 0.06

type ('b , 'a) _exec =
  { mutable i_96 : 'b ; mutable m_89 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_96 = (false:bool) ;
      m_89 = ((42. , 42. , 42. , 42. , 42. , 42.):float *
                                                  float *
                                                  float *
                                                  float * float * float) } in
  let exec_reset self  =
    (self.i_96 <- true:unit) in 
  let exec_step self () =
    (((if self.i_96 then self.m_89 <- (0. , vfi , amax , xli , vfi , 0.)) ;
      self.i_96 <- false ;
      (let ((x_90:float) ,
            (x_91:float) ,
            (x_92:float) , (x_93:float) , (x_94:float) , (x_95:float)) =
           self.m_89 in
       let (((xf_83:float) ,
             (vf_81:float) ,
             (af_79:float) , (xl_84:float) , (vl_82:float) , (al_80:float)): 
           (float  * float  * float  * float  * float  * float)) =
           (x_90 , x_91 , x_92 , x_93 , x_94 , x_95) in
       let (vl_next_85:float) = robot_get "v_l" in
       let (xl_next_86:float) = robot_get "x_l" in
       let (v_next_87:float) = robot_get "v_f" in
       let (x_next_88:float) = robot_get "x_f" in
       self.m_89 <- (x_next_88 ,
                     v_next_87 ,
                     (if (>=) ((+.) ((+.) ((+.) ((+.) x_next_88 
                                                      ((/.) (( *. ) v_next_87
                                                                    
                                                                    v_next_87)
                                                             (( *. ) 2.  b)))
                                                
                                                (( *. ) ((+.) 1. 
                                                              ((/.) amax  b))
                                                        
                                                        ((+.) (( *. ) 
                                                                 (( *. ) 
                                                                    2.  dt) 
                                                                 v_next_87) 
                                                              ((/.) (
                                                                    ( *. ) 
                                                                    amax 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    4.  dt) 
                                                                    dt))  
                                                                    2.)))) 
                                          ((/.) (( *. ) v_next_87  dt)  2.)) 
                                    0.5) 
                              ((+.) ((+.) xl_next_86 
                                          ((/.) (( *. ) ((-.) vl_next_85 
                                                              (( *. ) b  dt))
                                                        
                                                        ((-.) vl_next_85 
                                                              (( *. ) b  dt)))
                                                 (( *. ) 2.  b))) 
                                    ((/.) (( *. ) ((-.) vl_next_85 
                                                        (( *. ) b  dt))  
                                                  dt)  2.))
                      then (~-.) b
                      else amax) ,
                     xl_next_86 ,
                     vl_next_85 ,
                     (if (>=) xl_next_86  xbrake then (~-.) b else 0.)) ;
       (let _ = robot_str_ml ("accel") (af_79) in
        (xf_83 , vf_81 , af_79 , xl_84 , vl_82 , al_80)))):float *
                                                           float *
                                                           float *
                                                           float *
                                                           float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_98 : 'g ;
    mutable h_105 : 'f ;
    mutable i_103 : 'e ;
    mutable h_101 : 'd ;
    mutable result_100 : 'c ; mutable i_129 : 'b ; mutable m_122 : 'a }

let main (cstate_130:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_98 = false ;
      h_105 = 42. ;
      i_103 = (false:bool) ;
      h_101 = (42.:float) ;
      result_100 = (():unit) ;
      i_129 = (false:bool) ;
      m_122 = ((42. , 42. , 42. , 42. , 42. , 42.):float *
                                                   float *
                                                   float *
                                                   float * float * float) } in
  let main_step self ((time_97:float) , ()) =
    ((self.major_98 <- cstate_130.major ;
      (let (result_135:unit) =
           let h_104 = ref (infinity:float) in
           (if self.i_103 then self.h_101 <- (+.) time_97  0.) ;
           (let (z_102:bool) = (&&) self.major_98  ((>=) time_97  self.h_101) in
            self.h_101 <- (if z_102 then (+.) self.h_101  dt else self.h_101)
            ;
            h_104 := min !h_104  self.h_101 ;
            self.h_105 <- !h_104 ;
            self.i_103 <- false ;
            (let (trigger_99:zero) = z_102 in
             (begin match trigger_99 with
                    | true ->
                        (if self.i_129 then
                         self.m_122 <- (0. , vfi , amax , xli , vfi , 0.)) ;
                        self.i_129 <- false ;
                        (let () = () in
                         let ((x_123:float) ,
                              (x_124:float) ,
                              (x_125:float) ,
                              (x_126:float) , (x_127:float) , (x_128:float)) =
                             self.m_122 in
                         let (((xf_116:float) ,
                               (vf_114:float) ,
                               (af_112:float) ,
                               (xl_117:float) ,
                               (vl_115:float) , (al_113:float)): (float  *
                                                                  float  *
                                                                  float  *
                                                                  float  *
                                                                  float  *
                                                                  float)) =
                             (x_123 , x_124 , x_125 , x_126 , x_127 , x_128) in
                         let (vl_next_118:float) = robot_get "v_l" in
                         let (xl_next_119:float) = robot_get "x_l" in
                         let (v_next_120:float) = robot_get "v_f" in
                         let (x_next_121:float) = robot_get "x_f" in
                         self.m_122 <- (x_next_121 ,
                                        v_next_120 ,
                                        (if (>=) ((+.) ((+.) ((+.) ((+.) 
                                                                    x_next_121
                                                                    
                                                                    (
                                                                    (/.) 
                                                                    (
                                                                    ( *. ) 
                                                                    v_next_120
                                                                    
                                                                    v_next_120)
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    2.  b))) 
                                                                   (( *. ) 
                                                                    (
                                                                    (+.) 
                                                                    1. 
                                                                    (
                                                                    (/.) 
                                                                    amax  b))
                                                                    
                                                                    (
                                                                    (+.) 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    2.  dt) 
                                                                    v_next_120)
                                                                    
                                                                    (
                                                                    (/.) 
                                                                    (
                                                                    ( *. ) 
                                                                    amax 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    4.  dt) 
                                                                    dt))  
                                                                    2.)))) 
                                                             ((/.) (( *. ) 
                                                                    v_next_120
                                                                     
                                                                    dt)  
                                                                   2.))  
                                                       0.5) 
                                                 ((+.) ((+.) xl_next_119 
                                                             ((/.) (( *. ) 
                                                                    (
                                                                    (-.) 
                                                                    vl_next_118
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    b  dt)) 
                                                                    (
                                                                    (-.) 
                                                                    vl_next_118
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    b  dt))) 
                                                                   (( *. ) 
                                                                    2.  b))) 
                                                       ((/.) (( *. ) 
                                                                ((-.) 
                                                                   vl_next_118
                                                                   
                                                                   (( *. ) 
                                                                    b  dt)) 
                                                                dt)  
                                                             2.))
                                         then (~-.) b
                                         else amax) ,
                                        xl_next_119 ,
                                        vl_next_118 ,
                                        (if (>=) xl_next_119  xbrake
                                         then (~-.) b
                                         else 0.)) ;
                         (let _ = robot_str_ml ("accel") (af_112) in
                          let (al_107:float) = al_113 in
                          let (vl_109:float) = vl_115 in
                          let (xl_111:float) = xl_117 in
                          let (a_106:float) = af_112 in
                          let (v_108:float) = vf_114 in
                          let (x_110:float) = xf_116 in
                          let _ = print_float x_110 in
                          let _ = print_string "," in
                          let _ = print_float v_108 in
                          let _ = print_string "," in
                          let _ = print_float a_106 in
                          let _ = print_string "," in
                          let _ = print_float xl_111 in
                          let _ = print_string "," in
                          let _ = print_float vl_109 in
                          let _ = print_string "," in
                          let _ = print_float al_107 in
                          self.result_100 <- print_newline ()))
                    | _ -> self.result_100 <- ()  end) ; self.result_100)) in
       cstate_130.horizon <- min cstate_130.horizon  self.h_105 ; result_135)):
    unit) in 
  let main_reset self  =
    ((self.i_103 <- true ; self.i_129 <- true):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
