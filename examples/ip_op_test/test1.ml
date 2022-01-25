(* The Zelus compiler, version 2.1-dev
  (2022-01-25-14:12) *)
open Ztypes
external move_robot_ml: int -> unit = "move_robot_cpp" 

  
 external robot_get: string -> float = "robot_get_cpp" 

  
 external robot_str_ml: string -> float -> unit = "robot_str_cpp" 
 external control_robot_ml: int -> int -> unit = "control_robot_c" 

  
 external robot_store: string -> float -> unit = "robot_store_c" 
 
  
 external robot_store_ml: string -> unit = "robot_store_op" 
 
  
 external robot_get_ml: string -> unit = "robot_get_ip" 
 let y = 4.

"y" is an output variable using the lcm channel "chan"

type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_16 : 'e ;
    mutable h_23 : 'd ;
    mutable i_21 : 'c ; mutable h_19 : 'b ; mutable result_18 : 'a }

let main (cstate_24:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_16 = false ;
      h_23 = 42. ;
      i_21 = (false:bool) ; h_19 = (42.:float) ; result_18 = (():unit) } in
  let main_step self ((time_15:float) , ()) =
    ((self.major_16 <- cstate_24.major ;
      (let (result_29:unit) =
           let h_22 = ref (infinity:float) in
           (if self.i_21 then self.h_19 <- (+.) time_15  0.) ;
           (let (z_20:bool) = (&&) self.major_16  ((>=) time_15  self.h_19) in
            self.h_19 <- (if z_20 then (+.) self.h_19  1. else self.h_19) ;
            h_22 := min !h_22  self.h_19 ;
            self.h_23 <- !h_22 ;
            self.i_21 <- false ;
            (let (trigger_17:zero) = z_20 in
             (begin match trigger_17 with
                    | true ->
                        let _ = print_float y in
                        self.result_18 <- (robot_str_ml ("transverse_vel") (
                          (~-.) 30.)) | _ -> self.result_18 <- ()  end) ;
             (let () = self.result_18 in
              ()))) in
       cstate_24.horizon <- min cstate_24.horizon  self.h_23 ; result_29)):
    unit) in  let main_reset self  =
                (self.i_21 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
