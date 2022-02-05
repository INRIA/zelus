(* The Zelus compiler, version 2.1-dev
  (2022-01-27-8:16) *)
open Ztypes
external move_robot_ml: int -> unit = "move_robot_c" 
 
 external robot_store: string * float -> unit = "robot_store_c" 
 type ('e , 'd , 'c , 'b , 'a) _main =
   { mutable major_19 : 'e ;
     mutable h_26 : 'd ;
     mutable i_24 : 'c ; mutable h_22 : 'b ; mutable result_21 : 'a }

let main (cstate_28:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_19 = false ;
      h_26 = 42. ;
      i_24 = (false:bool) ; h_22 = (42.:float) ; result_21 = (():unit) } in
  let main_step self ((time_18:float) , ()) =
    ((self.major_19 <- cstate_28.major ;
      (let (result_33:unit) =
           let h_25 = ref (infinity:float) in
           (if self.i_24 then self.h_22 <- (+.) time_18  0.) ;
           (let (z_23:bool) = (&&) self.major_19  ((>=) time_18  self.h_22) in
            self.h_22 <- (if z_23 then (+.) self.h_22  1. else self.h_22) ;
            h_25 := min !h_25  self.h_22 ;
            self.h_26 <- !h_25 ;
            self.i_24 <- false ;
            (let (trigger_20:zero) = z_23 in
             (begin match trigger_20 with
                    | true ->
                        let (y_27:float) = 4. in
                        self.result_21 <- print_float y_27
                    | _ -> self.result_21 <- ()  end) ;
             (let () = self.result_21 in
              ()))) in
       cstate_28.horizon <- min cstate_28.horizon  self.h_26 ; result_33)):
    unit) in  let main_reset self  =
                (self.i_24 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
