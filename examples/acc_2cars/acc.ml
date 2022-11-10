(* The Zelus compiler, version 2.2-dev
  (2022-10-28-20:36) *)
open Ztypes
let vfi = 0.8

let dt = 0.1

let b = 0.136

let xli = 5.

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
    (((if self.i_96 then self.m_89 <- (0. , vfi , 0. , xli , vfi , ((~-.) b)))
      ;
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
       let (vl_next_85:float) =
           if (<) ((+.) vl_82  (( *. ) al_80  dt))  0.
           then 0.
           else (+.) vl_82  (( *. ) al_80  dt) in
       let (xl_next_86:float) = (+.) xl_84  (( *. ) vl_next_85  dt) in
       let (v_next_87:float) =
           if (<) ((+.) vf_81  (( *. ) af_79  dt))  0.
           then 0.
           else (+.) vf_81  (( *. ) af_79  dt) in
       let (x_next_88:float) = (+.) xf_83  (( *. ) v_next_87  dt) in
       self.m_89 <- (x_next_88 ,
                     v_next_87 ,
                     (if (>=) ((+.) ((+.) ((+.) x_next_88 
                                                ((/.) (( *. ) v_next_87 
                                                              v_next_87) 
                                                      (( *. ) 2.  b))) 
                                          (( *. ) v_next_87  dt)) 
                                    ((/.) (( *. ) v_next_87  dt)  2.)) 
                              ((+.) xl_next_86 
                                    ((/.) (( *. ) vl_next_85  vl_next_85) 
                                          (( *. ) 2.  b)))
                      then (~-.) b
                      else 0.) , xl_next_86 , vl_next_85 , ((~-.) b)) ;
       (xf_83 , vf_81 , af_79 , xl_84 , vl_82 , al_80))):float *
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
            (begin match z_102 with
                   | true ->
                       (if self.i_129 then
                        self.m_122 <- (0. , vfi , 0. , xli , vfi , ((~-.) b)))
                       ;
                       self.i_129 <- false ;
                       (let ((x_123:float) ,
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
                        let (vl_next_118:float) =
                            if (<) ((+.) vl_115  (( *. ) al_113  dt))  0.
                            then 0.
                            else (+.) vl_115  (( *. ) al_113  dt) in
                        let (xl_next_119:float) =
                            (+.) xl_117  (( *. ) vl_next_118  dt) in
                        let (v_next_120:float) =
                            if (<) ((+.) vf_114  (( *. ) af_112  dt))  0.
                            then 0.
                            else (+.) vf_114  (( *. ) af_112  dt) in
                        let (x_next_121:float) =
                            (+.) xf_116  (( *. ) v_next_120  dt) in
                        self.m_122 <- (x_next_121 ,
                                       v_next_120 ,
                                       (if (>=) ((+.) ((+.) ((+.) x_next_121 
                                                                  ((/.) 
                                                                    (
                                                                    ( *. ) 
                                                                    v_next_120
                                                                    
                                                                    v_next_120)
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    2.  b))) 
                                                            (( *. ) v_next_120
                                                                     
                                                                    dt)) 
                                                      ((/.) (( *. ) v_next_120
                                                                     
                                                                    dt)  
                                                            2.)) 
                                                ((+.) xl_next_119 
                                                      ((/.) (( *. ) vl_next_118
                                                                    
                                                                    vl_next_118)
                                                             (( *. ) 2.  b)))
                                        then (~-.) b
                                        else 0.) ,
                                       xl_next_119 , vl_next_118 , ((~-.) b))
                        ;
                        (let _ = print_float xf_116 in
                         let _ = print_string ";" in
                         let _ = print_float xl_117 in
                         self.result_100 <- print_newline ()))
                   | _ -> self.result_100 <- ()  end) ; self.result_100) in
       cstate_130.horizon <- min cstate_130.horizon  self.h_105 ; result_135)):
    unit) in 
  let main_reset self  =
    ((self.i_103 <- true ; self.i_129 <- true):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
