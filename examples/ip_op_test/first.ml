(* The Zelus compiler, version 2.1-dev
  (2022-01-10-12:3) *)
open Ztypes
external move_robot_ml: int -> unit = "move_robot_cpp" 

  
 external robot_get: string -> float = "robot_get_cpp" 

  
 external robot_str_ml: string -> float -> unit = "robot_str_cpp" 
 external control_robot_ml: int -> int -> unit = "control_robot_c" 

  
 external robot_store: string -> float -> unit = "robot_store_c" 
 
  
 external robot_store_ml: string -> unit = "robot_store_op" 
 
  
 external robot_get_ml: string -> unit = "robot_get_ip" 
 type state__164 = First_Second_15 | First_First_14 
let transverse_vel = 5

type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_29 : 'i ;
    mutable h_41 : 'h ;
    mutable h_39 : 'g ;
    mutable i_37 : 'f ;
    mutable h_35 : 'e ;
    mutable r_34 : 'd ;
    mutable s_33 : 'c ; mutable result_32 : 'b ; mutable t_30 : 'a }

let main (cstate_42:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_29 = false ;
      h_41 = 42. ;
      h_39 = (42.:float) ;
      i_37 = (false:bool) ;
      h_35 = (42.:float) ;
      r_34 = (false:bool) ;
      s_33 = (First_Second_15:state__164) ;
      result_32 = (():unit) ; t_30 = (42.:float) } in
  let main_step self ((time_28:float) , ()) =
    ((self.major_29 <- cstate_42.major ;
      (let (result_47:unit) =
           let h_40 = ref (infinity:float) in
           let encore_38 = ref (false:bool) in
           (if self.i_37 then self.h_35 <- (+.) time_28  0.) ;
           (let (z_36:bool) = (&&) self.major_29  ((>=) time_28  self.h_35) in
            let (trigger_31:zero) = z_36 in
            (begin match self.s_33 with
                   | First_First_14 ->
                       (if self.r_34 then ()) ;
                       self.t_30 <- (robot_get "transverse_vel") ;
                       (begin match trigger_31 with
                              | true ->
                                  encore_38 := true ;
                                  self.r_34 <- true ;
                                  self.s_33 <- First_Second_15
                              | _ -> self.r_34 <- false  end)
                   | First_Second_15 ->
                       (if self.r_34 then ()) ;
                       self.t_30 <- (robot_get "angular_vel") ;
                       (begin match trigger_31 with
                              | true ->
                                  encore_38 := true ;
                                  self.r_34 <- true ;
                                  self.s_33 <- First_First_14
                              | _ -> self.r_34 <- false  end)
                    end) ;
            self.h_39 <- (if !encore_38 then 0. else infinity) ;
            self.h_35 <- (if z_36 then (+.) self.h_35  1. else self.h_35) ;
            h_40 := min !h_40  (min self.h_39  self.h_35) ;
            self.h_41 <- !h_40 ;
            self.i_37 <- false ;
            (begin match trigger_31 with
                   | true ->
                       let _ = robot_store_ml "inp_chan" in
                       let _ = print_int 0 in
                       let _ = print_float self.t_30 in
                       let _ = print_newline () in
                       self.result_32 <- (robot_str_ml ("transverse_vel") (
                         (~-.) 30.)) | _ -> self.result_32 <- ()  end) ;
            (let () = self.result_32 in
             let () = robot_store_ml "inp_chan" in
             ())) in
       cstate_42.horizon <- min cstate_42.horizon  self.h_41 ; result_47)):
    unit) in 
  let main_reset self  =
    ((self.r_34 <- false ; self.s_33 <- First_First_14 ; self.i_37 <- true):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
