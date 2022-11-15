(* The Zelus compiler, version 2.2-dev
  (2022-11-10-21:54) *)
open Ztypes

   external robot_get: string -> float = "robot_get_cpp" 

   external robot_str_ml: string -> float -> unit = "robot_str_cpp" 

   external lcm_start: unit -> int = "LCM_start" 
 
   external lcm_stop: unit -> unit = "LCM_stop" 

  
 let () = ignore(lcm_start())
let dt = 0.02

let vi = 0.5

type ('b , 'a) _exec =
  { mutable i_36 : 'b ; mutable m_34 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ i_36 = (false:bool) ; m_34 = (42.:float) } in
  let exec_reset self  =
    (self.i_36 <- true:unit) in 
  let exec_step self () =
    (((if self.i_36 then self.m_34 <- vi) ;
      self.i_36 <- false ;
      (let (x_35:float) = self.m_34 in
       let (v_33:float) = x_35 in
       let (a_32:float) = robot_get "accel" in
       self.m_34 <- (if (<) ((+.) v_33  (( *. ) a_32  dt))  0.
                     then 0.
                     else (+.) v_33  (( *. ) a_32  dt)) ;
       (let _ = robot_str_ml ("transverse_vel") (v_33) in
        v_33))):float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_38 : 'g ;
    mutable h_45 : 'f ;
    mutable i_43 : 'e ;
    mutable h_41 : 'd ;
    mutable result_40 : 'c ; mutable i_51 : 'b ; mutable m_49 : 'a }

let main (cstate_52:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_38 = false ;
      h_45 = 42. ;
      i_43 = (false:bool) ;
      h_41 = (42.:float) ;
      result_40 = (():unit) ; i_51 = (false:bool) ; m_49 = (42.:float) } in
  let main_step self ((time_37:float) , ()) =
    ((self.major_38 <- cstate_52.major ;
      (let (result_57:unit) =
           let h_44 = ref (infinity:float) in
           (if self.i_43 then self.h_41 <- (+.) time_37  0.) ;
           (let (z_42:bool) = (&&) self.major_38  ((>=) time_37  self.h_41) in
            self.h_41 <- (if z_42 then (+.) self.h_41  dt else self.h_41) ;
            h_44 := min !h_44  self.h_41 ;
            self.h_45 <- !h_44 ;
            self.i_43 <- false ;
            (let (trigger_39:zero) = z_42 in
             (begin match trigger_39 with
                    | true ->
                        (if self.i_51 then self.m_49 <- vi) ;
                        self.i_51 <- false ;
                        (let () = () in
                         let (x_50:float) = self.m_49 in
                         let (v_48:float) = x_50 in
                         let (a_47:float) = robot_get "accel" in
                         self.m_49 <- (if (<) ((+.) v_48  (( *. ) a_47  dt)) 
                                              0.
                                       then 0.
                                       else (+.) v_48  (( *. ) a_47  dt)) ;
                         (let _ = robot_str_ml ("transverse_vel") (v_48) in
                          let (v_46:float) = v_48 in
                          let _ = print_float v_46 in
                          self.result_40 <- print_newline ()))
                    | _ -> self.result_40 <- ()  end) ; self.result_40)) in
       cstate_52.horizon <- min cstate_52.horizon  self.h_45 ; result_57)):
    unit) in 
  let main_reset self  =
    ((self.i_43 <- true ; self.i_51 <- true):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
