(* The Zelus compiler, version 2.2-dev
  (2022-06-16-21:23) *)
open Ztypes

   external robot_get: string -> float = "robot_get_cpp" 

   external robot_str_ml: string -> float -> unit = "robot_str_cpp" 

   external lcm_start: unit -> int = "LCM_start" 
 
   external lcm_stop: unit -> unit = "LCM_stop" 

  
 let () = ignore(lcm_start())
let pi = 3.1416

let x_last = 0.

let y_last = 0.

let theta_last = 0.

let wheel_base_half = 0.08125

type ('q ,
      'p ,
      'o ,
      'n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _exec =
  { mutable major_96 : 'q ;
    mutable h_127 : 'p ;
    mutable h_125 : 'o ;
    mutable i_123 : 'n ;
    mutable h_121 : 'm ;
    mutable h_119 : 'l ;
    mutable h_117 : 'k ;
    mutable result_111 : 'j ;
    mutable result_110 : 'i ;
    mutable result_109 : 'h ;
    mutable y_108 : 'g ;
    mutable x_107 : 'f ;
    mutable transverse_103 : 'e ;
    mutable theta_102 : 'd ;
    mutable d_right_99 : 'c ;
    mutable d_left_98 : 'b ; mutable angular_97 : 'a }

let exec (cstate_150:Ztypes.cstate) = 
  
  let exec_alloc _ =
    cstate_150.cmax <- (+) cstate_150.cmax  5;
    { major_96 = false ;
      h_127 = 42. ;
      h_125 = (42.:float) ;
      i_123 = (false:bool) ;
      h_121 = (42.:float) ;
      h_119 = (42.:float) ;
      h_117 = (42.:float) ;
      result_111 = (():unit) ;
      result_110 = ((42. , 42.):float * float) ;
      result_109 = ((42. , 42.):float * float) ;
      y_108 = { pos = 42.; der = 0. } ;
      x_107 = { pos = 42.; der = 0. } ;
      transverse_103 = (42.:float) ;
      theta_102 = { pos = 42.; der = 0. } ;
      d_right_99 = { pos = 42.; der = 0. } ;
      d_left_98 = { pos = 42.; der = 0. } ; angular_97 = (42.:float) } in
  let exec_step self ((time_95:float) , ()) =
    ((let (cindex_151:int) = cstate_150.cindex in
      let cpos_153 = ref (cindex_151:int) in
      cstate_150.cindex <- (+) cstate_150.cindex  5 ;
      self.major_96 <- cstate_150.major ;
      (if cstate_150.major then
       for i_1 = cindex_151 to 4 do Zls.set cstate_150.dvec  i_1  0. done
       else ((self.y_108.pos <- Zls.get cstate_150.cvec  !cpos_153 ;
              cpos_153 := (+) !cpos_153  1) ;
             (self.x_107.pos <- Zls.get cstate_150.cvec  !cpos_153 ;
              cpos_153 := (+) !cpos_153  1) ;
             (self.theta_102.pos <- Zls.get cstate_150.cvec  !cpos_153 ;
              cpos_153 := (+) !cpos_153  1) ;
             (self.d_right_99.pos <- Zls.get cstate_150.cvec  !cpos_153 ;
              cpos_153 := (+) !cpos_153  1) ;
             (self.d_left_98.pos <- Zls.get cstate_150.cvec  !cpos_153 ;
              cpos_153 := (+) !cpos_153  1))) ;
      (let (result_155:(float  * float  * float  * float  * float)) =
           let h_126 = ref (infinity:float) in
           let encore_124 = ref (false:bool) in
           (if self.i_123 then self.h_121 <- (+.) time_95  0.) ;
           (let (z_122:bool) = (&&) self.major_96  ((>=) time_95  self.h_121) in
            let (l_116:unit) = self.result_111 in
            (if self.i_123 then self.h_119 <- (+.) time_95  0.) ;
            (let (z_120:bool) =
                 (&&) self.major_96  ((>=) time_95  self.h_119) in
             let ((l_114:float) , (l_115:float)) = self.result_110 in
             (begin match z_120 with
                    | true ->
                        encore_124 := true ;
                        self.result_110 <- ((robot_get "odometry_x") ,
                                            (robot_get "odometry_y"))
                    | _ -> ()  end) ;
             (let ((odoemtry_x_100:float) , (odoemtry_y_101:float)) =
                  self.result_110 in
              (begin match z_122 with
                     | true ->
                         encore_124 := true ;
                         (let _ = print_float odoemtry_x_100 in
                          self.result_111 <- print_newline ()) | _ -> ()  end)
              ;
              (if self.i_123 then self.h_117 <- (+.) time_95  0.) ;
              (let (z_118:bool) =
                   (&&) self.major_96  ((>=) time_95  self.h_117) in
               let ((l_112:float) , (l_113:float)) = self.result_109 in
               (begin match z_118 with
                      | true ->
                          encore_124 := true ;
                          (let _ = robot_str_ml ("transverse_vel") (0.5) in
                           let _ = robot_str_ml ("angular_vel") (0.5) in
                           self.result_109 <- (0.5 , 0.5)) | _ -> ()  end) ;
               self.h_125 <- (if !encore_124 then 0. else infinity) ;
               self.h_121 <- (if z_122
                              then (+.) self.h_121  0.04
                              else self.h_121) ;
               self.h_119 <- (if z_120
                              then (+.) self.h_119  0.04
                              else self.h_119) ;
               self.h_117 <- (if z_118
                              then (+.) self.h_117  0.04
                              else self.h_117) ;
               h_126 := min !h_126 
                            (min (min (min self.h_125  self.h_121) 
                                      self.h_119)  self.h_117) ;
               self.h_127 <- !h_126 ;
               self.i_123 <- false ;
               (let (var_104:unit) = self.result_111 in
                let ((copy_147:float) , (copy_148:float)) = self.result_109 in
                self.transverse_103 <- copy_147 ;
                (let (vy_106:float) =
                     ( *. ) self.transverse_103  (sin self.theta_102.pos) in
                 self.y_108.der <- vy_106 ;
                 (let (vx_105:float) =
                      ( *. ) self.transverse_103  (cos self.theta_102.pos) in
                  self.x_107.der <- vx_105 ;
                  self.angular_97 <- copy_148 ;
                  self.theta_102.der <- self.angular_97 ;
                  self.d_right_99.der <- (+.) self.transverse_103 
                                              (( *. ) self.angular_97 
                                                      wheel_base_half) ;
                  self.d_left_98.der <- (-.) self.transverse_103 
                                             (( *. ) self.angular_97 
                                                     wheel_base_half) ;
                  (self.x_107.pos ,
                   self.y_108.pos ,
                   self.theta_102.pos ,
                   self.d_left_98.pos , self.d_right_99.pos)))))))) in
       cstate_150.horizon <- min cstate_150.horizon  self.h_127 ;
       cpos_153 := cindex_151 ;
       (if cstate_150.major then
        (((Zls.set cstate_150.cvec  !cpos_153  self.y_108.pos ;
           cpos_153 := (+) !cpos_153  1) ;
          (Zls.set cstate_150.cvec  !cpos_153  self.x_107.pos ;
           cpos_153 := (+) !cpos_153  1) ;
          (Zls.set cstate_150.cvec  !cpos_153  self.theta_102.pos ;
           cpos_153 := (+) !cpos_153  1) ;
          (Zls.set cstate_150.cvec  !cpos_153  self.d_right_99.pos ;
           cpos_153 := (+) !cpos_153  1) ;
          (Zls.set cstate_150.cvec  !cpos_153  self.d_left_98.pos ;
           cpos_153 := (+) !cpos_153  1)))
        else (((Zls.set cstate_150.dvec  !cpos_153  self.y_108.der ;
                cpos_153 := (+) !cpos_153  1) ;
               (Zls.set cstate_150.dvec  !cpos_153  self.x_107.der ;
                cpos_153 := (+) !cpos_153  1) ;
               (Zls.set cstate_150.dvec  !cpos_153  self.theta_102.der ;
                cpos_153 := (+) !cpos_153  1) ;
               (Zls.set cstate_150.dvec  !cpos_153  self.d_right_99.der ;
                cpos_153 := (+) !cpos_153  1) ;
               (Zls.set cstate_150.dvec  !cpos_153  self.d_left_98.der ;
                cpos_153 := (+) !cpos_153  1)))) ; result_155)):float *
                                                                float *
                                                                float *
                                                                float * float) in
  
  let exec_reset self  =
    ((self.result_111 <- () ;
      self.i_123 <- true ;
      self.result_110 <- (0. , 0.) ;
      self.result_109 <- (0. , 0.) ;
      self.transverse_103 <- 0.5 ;
      self.theta_102.pos <- 0. ;
      self.y_108.pos <- (-0.5) ;
      self.x_107.pos <- 0.5 ;
      self.angular_97 <- 0.5 ;
      self.d_right_99.pos <- 0. ; self.d_left_98.pos <- 0.):unit) in
  Node { alloc = exec_alloc; step = exec_step ; reset = exec_reset }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_149 : 'h ;
    mutable major_129 : 'g ;
    mutable h_141 : 'f ;
    mutable i_139 : 'e ;
    mutable h_137 : 'd ;
    mutable i_146 : 'c ; mutable m_144 : 'b ; mutable m_142 : 'a }

let main (cstate_156:Ztypes.cstate) = 
  let Node { alloc = i_149_alloc; step = i_149_step ; reset = i_149_reset } = exec 
  cstate_156 in
  let main_alloc _ =
    ();
    { major_129 = false ;
      h_141 = 42. ;
      i_139 = (false:bool) ;
      h_137 = (42.:float) ;
      i_146 = (false:bool) ; m_144 = (42.:float) ; m_142 = (42.:float);
      i_149 = i_149_alloc () (* continuous *)  } in
  let main_step self ((time_128:float) , ()) =
    ((self.major_129 <- cstate_156.major ;
      (let (result_161:unit) =
           let h_140 = ref (infinity:float) in
           let resultp_136 = ref (false:bool) in
           let resultv_135 = ref (():unit) in
           (if self.i_139 then self.h_137 <- (+.) time_128  0.) ;
           (let (z_138:bool) =
                (&&) self.major_129  ((>=) time_128  self.h_137) in
            self.h_137 <- (if z_138
                           then (+.) self.h_137  0.04
                           else self.h_137) ;
            h_140 := min !h_140  self.h_137 ;
            self.h_141 <- !h_140 ;
            self.i_139 <- false ;
            (let ((x_133:float) ,
                  (y_134:float) ,
                  (theta_132:float) , (dl_130:float) , (dr_131:float)) =
                 i_149_step self.i_149 (time_128 , ()) in
             (begin match z_138 with
                    | true ->
                        (if self.i_146 then self.m_144 <- y_134) ;
                        (if self.i_146 then self.m_142 <- x_133) ;
                        self.i_146 <- false ;
                        resultp_136 := true ;
                        (let (x_145:float) = self.m_144 in
                         self.m_144 <- y_134 ;
                         (let (x_143:float) = self.m_142 in
                          self.m_142 <- x_133 ;
                          (let _ =
                               Drawrobot.show_robot x_133 
                                                    x_143 
                                                    y_134  x_145  theta_132 in
                           resultv_135 := ()))) | _ -> ()  end) ;
             (let _ = (!resultv_135 , !resultp_136) in
              ()))) in
       cstate_156.horizon <- min cstate_156.horizon  self.h_141 ; result_161)):
    unit) in 
  let main_reset self  =
    ((self.i_139 <- true ; i_149_reset self.i_149  ; self.i_146 <- true):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
