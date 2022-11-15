(* The Zelus compiler, version 2.2-dev
  (2022-11-10-21:54) *)
open Ztypes

   external robot_get: string -> float = "robot_get_cpp" 

   external robot_str_ml: string -> float -> unit = "robot_str_cpp" 

   external lcm_start: unit -> int = "LCM_start" 
 
   external lcm_stop: unit -> unit = "LCM_stop" 

  
 let () = ignore(lcm_start())
let dt = 0.1

let b = 0.136

let vi = 0.5

let dbrake = 2.

type ('d , 'c , 'b , 'a) _exec =
  { mutable i_59 : 'd ;
    mutable m_57 : 'c ; mutable m_55 : 'b ; mutable m_53 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_59 = (false:bool) ;
      m_57 = (42.:float) ; m_55 = (42.:float) ; m_53 = (42.:float) } in
  let exec_reset self  =
    ((self.i_59 <- true ; self.m_57 <- 0. ; self.m_53 <- 0.):unit) in 
  let exec_step self () =
    (((if self.i_59 then self.m_55 <- vi) ;
      self.i_59 <- false ;
      (let (x_58:float) = self.m_57 in
       let (x_54:float) = self.m_53 in
       let (x_52:float) = robot_get "odometry_x" in
       self.m_57 <- (if (>=) x_52  dbrake then (~-.) b else 0.) ;
       (let (x_56:float) = self.m_55 in
        let (v_51:float) = x_56 in
        let (a_50:float) = x_58 in
        self.m_55 <- (if (<) ((+.) v_51  (( *. ) a_50  dt))  0.
                      then 0.
                      else (+.) v_51  (( *. ) a_50  dt)) ;
        self.m_53 <- (+.) x_52  (( *. ) v_51  dt) ;
        (let _ = robot_str_ml ("transverse_vel") (v_51) in
         (x_52 , v_51 , a_50))))):float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_61 : 'i ;
    mutable h_68 : 'h ;
    mutable i_66 : 'g ;
    mutable h_64 : 'f ;
    mutable result_63 : 'e ;
    mutable i_81 : 'd ;
    mutable m_79 : 'c ; mutable m_77 : 'b ; mutable m_75 : 'a }

let main (cstate_82:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_61 = false ;
      h_68 = 42. ;
      i_66 = (false:bool) ;
      h_64 = (42.:float) ;
      result_63 = (():unit) ;
      i_81 = (false:bool) ;
      m_79 = (42.:float) ; m_77 = (42.:float) ; m_75 = (42.:float) } in
  let main_step self ((time_60:float) , ()) =
    ((self.major_61 <- cstate_82.major ;
      (let (result_87:unit) =
           let h_67 = ref (infinity:float) in
           (if self.i_66 then self.h_64 <- (+.) time_60  0.) ;
           (let (z_65:bool) = (&&) self.major_61  ((>=) time_60  self.h_64) in
            self.h_64 <- (if z_65 then (+.) self.h_64  dt else self.h_64) ;
            h_67 := min !h_67  self.h_64 ;
            self.h_68 <- !h_67 ;
            self.i_66 <- false ;
            (let (trigger_62:zero) = z_65 in
             (begin match trigger_62 with
                    | true ->
                        (if self.i_81 then self.m_77 <- vi) ;
                        self.i_81 <- false ;
                        (let () = () in
                         let (x_80:float) = self.m_79 in
                         let (x_76:float) = self.m_75 in
                         let (x_74:float) = robot_get "odometry_x" in
                         self.m_79 <- (if (>=) x_74  dbrake
                                       then (~-.) b
                                       else 0.) ;
                         (let (x_78:float) = self.m_77 in
                          let (v_73:float) = x_78 in
                          let (a_72:float) = x_80 in
                          self.m_77 <- (if (<) ((+.) v_73  (( *. ) a_72  dt))
                                                0.
                                        then 0.
                                        else (+.) v_73  (( *. ) a_72  dt)) ;
                          self.m_75 <- (+.) x_74  (( *. ) v_73  dt) ;
                          (let _ = robot_str_ml ("transverse_vel") (v_73) in
                           let (a_69:float) = a_72 in
                           let (v_70:float) = v_73 in
                           let (x_71:float) = x_74 in
                           let _ = print_float x_71 in
                           let _ = print_string "," in
                           let _ = print_float v_70 in
                           let _ = print_string "," in
                           let _ = print_float a_69 in
                           self.result_63 <- print_newline ())))
                    | _ -> self.result_63 <- ()  end) ; self.result_63)) in
       cstate_82.horizon <- min cstate_82.horizon  self.h_68 ; result_87)):
    unit) in 
  let main_reset self  =
    ((self.i_66 <- true ;
      self.i_81 <- true ; self.m_79 <- 0. ; self.m_75 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
