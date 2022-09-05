(* The Zelus compiler, version 2.2-dev
  (2022-09-5-13:49) *)
open Ztypes

   external robot_get: string -> float = "robot_get_cpp" 

   external robot_str_ml: string -> float -> unit = "robot_str_cpp" 

   external lcm_start: unit -> int = "LCM_start" 
 
   external lcm_stop: unit -> unit = "LCM_stop" 

  
 let () = ignore(lcm_start())
type _exec = unit

let exec  = 
   let exec_alloc _ = () in
  let exec_reset self  =
    ((()):unit) in 
  let exec_step self () =
    ((let (x_19:float) = robot_get "x" in
      x_19):float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_21 : 'e ;
    mutable h_28 : 'd ;
    mutable i_26 : 'c ; mutable h_24 : 'b ; mutable result_23 : 'a }

let main (cstate_30:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_21 = false ;
      h_28 = 42. ;
      i_26 = (false:bool) ; h_24 = (42.:float) ; result_23 = (():unit) } in
  let main_step self ((time_20:float) , ()) =
    ((self.major_21 <- cstate_30.major ;
      (let (result_35:unit) =
           let h_27 = ref (infinity:float) in
           (if self.i_26 then self.h_24 <- (+.) time_20  0.) ;
           (let (z_25:bool) = (&&) self.major_21  ((>=) time_20  self.h_24) in
            self.h_24 <- (if z_25 then (+.) self.h_24  0.1 else self.h_24) ;
            h_27 := min !h_27  self.h_24 ;
            self.h_28 <- !h_27 ;
            self.i_26 <- false ;
            (begin match z_25 with
                   | true ->
                       let (x_29:float) = robot_get "x" in
                       self.result_23 <- print_float x_29
                   | _ -> self.result_23 <- ()  end) ; self.result_23) in
       cstate_30.horizon <- min cstate_30.horizon  self.h_28 ; result_35)):
    unit) in  let main_reset self  =
                (self.i_26 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
