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
 type state__169 =
 Test_StopB_21 | Test_Backward_20 | Test_StopF_19 | Test_Forward_18 
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_35 : 'i ;
    mutable h_47 : 'h ;
    mutable h_45 : 'g ;
    mutable i_43 : 'f ;
    mutable h_41 : 'e ;
    mutable r_40 : 'd ;
    mutable s_39 : 'c ; mutable result_38 : 'b ; mutable vel1_37 : 'a }

let main (cstate_48:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_35 = false ;
      h_47 = 42. ;
      h_45 = (42.:float) ;
      i_43 = (false:bool) ;
      h_41 = (42.:float) ;
      r_40 = (false:bool) ;
      s_39 = (Test_StopB_21:state__169) ;
      result_38 = (():unit) ; vel1_37 = (42:int) } in
  let main_step self ((time_34:float) , ()) =
    ((self.major_35 <- cstate_48.major ;
      (let (result_53:unit) =
           let h_46 = ref (infinity:float) in
           let encore_44 = ref (false:bool) in
           (if self.i_43 then self.h_41 <- (+.) time_34  0.) ;
           (let (z_42:bool) = (&&) self.major_35  ((>=) time_34  self.h_41) in
            let (trigger_36:zero) = z_42 in
            (begin match self.s_39 with
                   | Test_Forward_18 ->
                       (if self.r_40 then ()) ;
                       self.vel1_37 <- 30 ;
                       (begin match trigger_36 with
                              | true ->
                                  encore_44 := true ;
                                  self.r_40 <- true ;
                                  self.s_39 <- Test_StopF_19
                              | _ -> self.r_40 <- false  end)
                   | Test_StopF_19 ->
                       (if self.r_40 then ()) ;
                       self.vel1_37 <- 0 ;
                       (begin match trigger_36 with
                              | true ->
                                  encore_44 := true ;
                                  self.r_40 <- true ;
                                  self.s_39 <- Test_Backward_20
                              | _ -> self.r_40 <- false  end)
                   | Test_Backward_20 ->
                       (if self.r_40 then ()) ;
                       self.vel1_37 <- (-30) ;
                       (begin match trigger_36 with
                              | true ->
                                  encore_44 := true ;
                                  self.r_40 <- true ;
                                  self.s_39 <- Test_StopB_21
                              | _ -> self.r_40 <- false  end)
                   | Test_StopB_21 ->
                       (if self.r_40 then ()) ;
                       self.vel1_37 <- 0 ;
                       (begin match trigger_36 with
                              | true ->
                                  encore_44 := true ;
                                  self.r_40 <- true ;
                                  self.s_39 <- Test_Forward_18
                              | _ -> self.r_40 <- false  end)
                    end) ;
            self.h_45 <- (if !encore_44 then 0. else infinity) ;
            self.h_41 <- (if z_42 then (+.) self.h_41  1. else self.h_41) ;
            h_46 := min !h_46  (min self.h_45  self.h_41) ;
            self.h_47 <- !h_46 ;
            self.i_43 <- false ;
            (begin match trigger_36 with
                   | true ->
                       let _ = print_int self.vel1_37 in
                       let _ = print_int ((~-) self.vel1_37) in
                       let _ = print_newline () in
                       self.result_38 <- (control_robot_ml (self.vel1_37) (
                         (~-) self.vel1_37)) | _ -> self.result_38 <- ()  end)
            ; (let () = self.result_38 in
               ())) in
       cstate_48.horizon <- min cstate_48.horizon  self.h_47 ; result_53)):
    unit) in 
  let main_reset self  =
    ((self.r_40 <- false ; self.s_39 <- Test_Forward_18 ; self.i_43 <- true):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
