(* The Zelus compiler, version 2.1-dev
  (2021-09-19-20:48) *)
open Ztypes
external move_robot_ml: int -> unit = "move_robot_cpp" 

 external robot_get: float -> unit = "robot_get_cpp" 
 external control_robot_ml: int -> int -> unit = "control_robot_c" 

 external robot_store: string -> float -> unit = "robot_store_c" 
 let pi = 3.14159

let w = ( *. ) pi  2.

let y0 = 1.

let y'0 = 0.

let key = 90.

type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_21 : 'f ;
    mutable i_26 : 'e ;
    mutable x_25 : 'd ;
    mutable y'_24 : 'c ; mutable y_23 : 'b ; mutable m_28 : 'a }

let main (cstate_30:Ztypes.cstate) = 
  
  let main_alloc _ =
    cstate_30.cmax <- (+) cstate_30.cmax  2 ;
    cstate_30.zmax <- (+) cstate_30.zmax  1;
    { major_21 = false ;
      i_26 = (false:bool) ;
      x_25 = { zin = false; zout = 1. } ;
      y'_24 = { pos = 42.; der = 0. } ;
      y_23 = { pos = 42.; der = 0. } ; m_28 = (42:int) } in
  let main_step self ((time_20:float) , ()) =
    ((let (cindex_31:int) = cstate_30.cindex in
      let cpos_33 = ref (cindex_31:int) in
      let (zindex_32:int) = cstate_30.zindex in
      let zpos_34 = ref (zindex_32:int) in
      cstate_30.cindex <- (+) cstate_30.cindex  2 ;
      cstate_30.zindex <- (+) cstate_30.zindex  1 ;
      self.major_21 <- cstate_30.major ;
      (if cstate_30.major then
       for i_1 = cindex_31 to 1 do Zls.set cstate_30.dvec  i_1  0. done
       else ((self.y'_24.pos <- Zls.get cstate_30.cvec  !cpos_33 ;
              cpos_33 := (+) !cpos_33  1) ;
             (self.y_23.pos <- Zls.get cstate_30.cvec  !cpos_33 ;
              cpos_33 := (+) !cpos_33  1))) ;
      (let (result_35:unit) =
           (if self.i_26 then self.y'_24.pos <- y'0) ;
           (if self.i_26 then self.y_23.pos <- y0) ;
           self.i_26 <- false ;
           (let (trigger_22:zero) = self.x_25.zin in
            (begin match trigger_22 with
                   | true ->
                       let () = robot_get key in
                       let (x_29:int) = self.m_28 in
                       let (cpt_27:int) = (+) x_29  1 in
                       self.m_28 <- cpt_27 | _ -> ()  end) ;
            self.x_25.zout <- self.y_23.pos ;
            self.y'_24.der <- ( *. ) (( *. ) ((~-.) w)  w)  self.y_23.pos ;
            self.y_23.der <- self.y'_24.pos ; ()) in
       cpos_33 := cindex_31 ;
       (if cstate_30.major then
        (((Zls.set cstate_30.cvec  !cpos_33  self.y'_24.pos ;
           cpos_33 := (+) !cpos_33  1) ;
          (Zls.set cstate_30.cvec  !cpos_33  self.y_23.pos ;
           cpos_33 := (+) !cpos_33  1)) ; ((self.x_25.zin <- false)))
        else (((self.x_25.zin <- Zls.get_zin cstate_30.zinvec  !zpos_34 ;
                zpos_34 := (+) !zpos_34  1)) ;
              zpos_34 := zindex_32 ;
              ((Zls.set cstate_30.zoutvec  !zpos_34  self.x_25.zout ;
                zpos_34 := (+) !zpos_34  1)) ;
              ((Zls.set cstate_30.dvec  !cpos_33  self.y'_24.der ;
                cpos_33 := (+) !cpos_33  1) ;
               (Zls.set cstate_30.dvec  !cpos_33  self.y_23.der ;
                cpos_33 := (+) !cpos_33  1)))) ; result_35)):unit) in 
  let main_reset self  =
    ((self.i_26 <- true ; self.m_28 <- 0):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
