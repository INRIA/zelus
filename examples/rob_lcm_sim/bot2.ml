(* The Zelus compiler, version 2.1-dev
  (2022-02-21-6:15) *)
open Ztypes
(*open Sys;;
(catch_break true)*)

   external robot_get: string -> float = "robot_get_cpp" 

   external robot_str_ml: string -> float -> unit = "robot_str_cpp" 

   external lcm_start: unit -> int = "LCM_start" 
 
   external lcm_stop: unit -> unit = "LCM_stop" 

  
 let () = ignore(lcm_start())
 let is_done = ref false;;
 
 let cleanup () = 
  is_done := true;
  print_string "Interrupted";
  print_newline ();
  lcm_stop ();;
 let testpos () =
  try print_string "trying";
  with Exit -> cleanup ();;
let pi = 3.1416

let x_last = 0.

let y_last = 0.

let theta_last = 0.

let wheel_base_half = 0.08125

type ('m , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _exec =
  { mutable major_75 : 'm ;
    mutable h_94 : 'l ;
    mutable h_92 : 'k ;
    mutable i_90 : 'j ;
    mutable h_88 : 'i ;
    mutable result_85 : 'h ;
    mutable y_84 : 'g ;
    mutable x_83 : 'f ;
    mutable transverse_80 : 'e ;
    mutable theta_79 : 'd ;
    mutable d_right_78 : 'c ;
    mutable d_left_77 : 'b ; mutable angular_76 : 'a }

let exec (cstate_117:Ztypes.cstate) = 
  
  let exec_alloc _ =
    cstate_117.cmax <- (+) cstate_117.cmax  5;
    { major_75 = false ;
      h_94 = 42. ;
      h_92 = (42.:float) ;
      i_90 = (false:bool) ;
      h_88 = (42.:float) ;
      result_85 = ((42. , 42.):float * float) ;
      y_84 = { pos = 42.; der = 0. } ;
      x_83 = { pos = 42.; der = 0. } ;
      transverse_80 = (42.:float) ;
      theta_79 = { pos = 42.; der = 0. } ;
      d_right_78 = { pos = 42.; der = 0. } ;
      d_left_77 = { pos = 42.; der = 0. } ; angular_76 = (42.:float) } in
  let exec_step self ((time_74:float) , ()) =
    ((let (cindex_118:int) = cstate_117.cindex in
      let cpos_120 = ref (cindex_118:int) in
      cstate_117.cindex <- (+) cstate_117.cindex  5 ;
      self.major_75 <- cstate_117.major ;
      (if cstate_117.major then
       for i_1 = cindex_118 to 4 do Zls.set cstate_117.dvec  i_1  0. done
       else ((self.y_84.pos <- Zls.get cstate_117.cvec  !cpos_120 ;
              cpos_120 := (+) !cpos_120  1) ;
             (self.x_83.pos <- Zls.get cstate_117.cvec  !cpos_120 ;
              cpos_120 := (+) !cpos_120  1) ;
             (self.theta_79.pos <- Zls.get cstate_117.cvec  !cpos_120 ;
              cpos_120 := (+) !cpos_120  1) ;
             (self.d_right_78.pos <- Zls.get cstate_117.cvec  !cpos_120 ;
              cpos_120 := (+) !cpos_120  1) ;
             (self.d_left_77.pos <- Zls.get cstate_117.cvec  !cpos_120 ;
              cpos_120 := (+) !cpos_120  1))) ;
      (let (result_122:(float  * float  * float  * float  * float)) =
           let h_93 = ref (infinity:float) in
           let encore_91 = ref (false:bool) in
           (if self.i_90 then self.h_88 <- (+.) time_74  0.) ;
           (let (z_89:bool) = (&&) self.major_75  ((>=) time_74  self.h_88) in
            let ((l_86:float) , (l_87:float)) = self.result_85 in
            (begin match z_89 with
                   | true ->
                       encore_91 := true ;
                       (let _ = robot_str_ml ("transverse_vel") (0.5) in
                        let _ = robot_str_ml ("angular_vel") (0.5) in
                        self.result_85 <- ((robot_get "transverse_vel") ,
                                           (robot_get "angular_vel")))
                   | _ -> ()  end) ;
            self.h_92 <- (if !encore_91 then 0. else infinity) ;
            self.h_88 <- (if z_89 then (+.) self.h_88  0.04 else self.h_88) ;
            h_93 := min !h_93  (min self.h_92  self.h_88) ;
            self.h_94 <- !h_93 ;
            self.i_90 <- false ;
            (let ((copy_114:float) , (copy_115:float)) = self.result_85 in
             self.transverse_80 <- copy_114 ;
             (let (vy_82:float) =
                  ( *. ) self.transverse_80  (sin self.theta_79.pos) in
              self.y_84.der <- vy_82 ;
              (let (vx_81:float) =
                   ( *. ) self.transverse_80  (cos self.theta_79.pos) in
               self.x_83.der <- vx_81 ;
               self.angular_76 <- copy_115 ;
               self.theta_79.der <- self.angular_76 ;
               self.d_right_78.der <- (+.) self.transverse_80 
                                           (( *. ) self.angular_76 
                                                   wheel_base_half) ;
               self.d_left_77.der <- (-.) self.transverse_80 
                                          (( *. ) self.angular_76 
                                                  wheel_base_half) ;
               (self.x_83.pos ,
                self.y_84.pos ,
                self.theta_79.pos , self.d_left_77.pos , self.d_right_78.pos))))) in
       cstate_117.horizon <- min cstate_117.horizon  self.h_94 ;
       cpos_120 := cindex_118 ;
       (if cstate_117.major then
        (((Zls.set cstate_117.cvec  !cpos_120  self.y_84.pos ;
           cpos_120 := (+) !cpos_120  1) ;
          (Zls.set cstate_117.cvec  !cpos_120  self.x_83.pos ;
           cpos_120 := (+) !cpos_120  1) ;
          (Zls.set cstate_117.cvec  !cpos_120  self.theta_79.pos ;
           cpos_120 := (+) !cpos_120  1) ;
          (Zls.set cstate_117.cvec  !cpos_120  self.d_right_78.pos ;
           cpos_120 := (+) !cpos_120  1) ;
          (Zls.set cstate_117.cvec  !cpos_120  self.d_left_77.pos ;
           cpos_120 := (+) !cpos_120  1)))
        else (((Zls.set cstate_117.dvec  !cpos_120  self.y_84.der ;
                cpos_120 := (+) !cpos_120  1) ;
               (Zls.set cstate_117.dvec  !cpos_120  self.x_83.der ;
                cpos_120 := (+) !cpos_120  1) ;
               (Zls.set cstate_117.dvec  !cpos_120  self.theta_79.der ;
                cpos_120 := (+) !cpos_120  1) ;
               (Zls.set cstate_117.dvec  !cpos_120  self.d_right_78.der ;
                cpos_120 := (+) !cpos_120  1) ;
               (Zls.set cstate_117.dvec  !cpos_120  self.d_left_77.der ;
                cpos_120 := (+) !cpos_120  1)))) ; result_122)):float *
                                                                float *
                                                                float *
                                                                float * float) in
  
  let exec_reset self  =
    ((self.result_85 <- (0. , 0.) ;
      self.i_90 <- true ;
      self.transverse_80 <- 0. ;
      self.theta_79.pos <- 0. ;
      self.y_84.pos <- (-0.5) ;
      self.x_83.pos <- 0.5 ;
      self.angular_76 <- 0. ;
      self.d_right_78.pos <- 0. ; self.d_left_77.pos <- 0.):unit) in
  Node { alloc = exec_alloc; step = exec_step ; reset = exec_reset }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_116 : 'h ;
    mutable major_96 : 'g ;
    mutable h_108 : 'f ;
    mutable i_106 : 'e ;
    mutable h_104 : 'd ;
    mutable i_113 : 'c ; mutable m_111 : 'b ; mutable m_109 : 'a }

let main (cstate_123:Ztypes.cstate) = 
  if !is_done then cleanup () else testpos ();
  let Node { alloc = i_116_alloc; step = i_116_step ; reset = i_116_reset } = exec 
  cstate_123 in
  let main_alloc _ =
    ();
    { major_96 = false ;
      h_108 = 42. ;
      i_106 = (false:bool) ;
      h_104 = (42.:float) ;
      i_113 = (false:bool) ; m_111 = (42.:float) ; m_109 = (42.:float);
      i_116 = i_116_alloc () (* continuous *)  } in
  let main_step self ((time_95:float) , ()) =
    ((self.major_96 <- cstate_123.major ;
      (let (result_128:unit) =
           let h_107 = ref (infinity:float) in
           let resultp_103 = ref (false:bool) in
           let resultv_102 = ref (():unit) in
           (if self.i_106 then self.h_104 <- (+.) time_95  0.) ;
           (let (z_105:bool) = (&&) self.major_96  ((>=) time_95  self.h_104) in
            self.h_104 <- (if z_105
                           then (+.) self.h_104  0.04
                           else self.h_104) ;
            h_107 := min !h_107  self.h_104 ;
            self.h_108 <- !h_107 ;
            self.i_106 <- false ;
            (let ((x_100:float) ,
                  (y_101:float) ,
                  (theta_99:float) , (dl_97:float) , (dr_98:float)) =
                 i_116_step self.i_116 (time_95 , ()) in
             (begin match z_105 with
                    | true ->
                        (if self.i_113 then self.m_111 <- y_101) ;
                        (if self.i_113 then self.m_109 <- x_100) ;
                        self.i_113 <- false ;
                        resultp_103 := true ;
                        (let (x_112:float) = self.m_111 in
                         self.m_111 <- y_101 ;
                         (let (x_110:float) = self.m_109 in
                          self.m_109 <- x_100 ;
                          (let _ =
                               Drawrobot.show_robot x_100 
                                                    x_110 
                                                    y_101  x_112  theta_99 in
                           resultv_102 := ()))) | _ -> ()  end) ;
             (let _ = (!resultv_102 , !resultp_103) in
              ()))) in
       cstate_123.horizon <- min cstate_123.horizon  self.h_108 ; result_128)):
    unit) in 
  let main_reset self  =
    ((self.i_106 <- true ; i_116_reset self.i_116  ; self.i_113 <- true):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset} 