(* The Zélus compiler, version 2.0
  (mardi 13 novembre 2018, 14:09:50 (UTC+0100)) *)
open Ztypes
type state__250 = State4_19 | State3_18 | State2_17 | State1_16 
type ('d, 'c, 'b, 'a) _passing_maneuver =
  { mutable x_24 : 'd;
    mutable nx_23 : 'c; mutable r_21 : 'b; mutable s_20 : 'a }

let passing_maneuver  = 
  
  let passing_maneuver_alloc _ =
    Zls.cmax := (+) (Pervasives.(!) Zls.cmax) 1;
    Zls.zmax := (+) (Pervasives.(!) Zls.zmax) 1;
    { x_24 = { zin = false; zout = 1. };
      nx_23 = { pos = 0.; der = 0. };
      r_21 = (false:bool); s_20 = (State4_19:state__250) } in
  let passing_maneuver_step self ((time_22:float), ()) =
    ((let (ci_27:int) = Pervasives.(!) Zls.cindex in
      let cpos_29 = ref (ci_27:int) in
      let (zi_28:int) = Pervasives.(!) Zls.zindex in
      let zpos_30 = ref (zi_28:int) in
      Zls.cindex := (+) (Pervasives.(!) Zls.cindex) 1;
      Zls.zindex := (+) (Pervasives.(!) Zls.zindex) 1;
      (if Pervasives.(!) Zls.discrete then
       for i_1 = ci_27 to 0 do Zls.set (Pervasives.(!) Zls.dvec) i_1 0. done
       else ((self.nx_23.pos <- Zls.get (Pervasives.(!) Zls.cvec) !cpos_29;
              cpos_29 := (+) !cpos_29 1)));
      (let (result_31:(float * float)) =
           let (throttle_15:float) = self.nx_23.pos in
           (match self.s_20 with
              | State1_16 ->
                  (if self.r_21 then ());
                  self.x_24.zout <- (-.) 40. throttle_15;
                  (match self.x_24.zin with
                     | true -> self.r_21 <- true; self.s_20 <- State2_17
                     | _ -> self.r_21 <- false )
              | State2_17 ->
                  (if self.r_21 then ());
                  self.x_24.zout <- (-.) throttle_15 100.;
                  (match self.x_24.zin with
                     | true -> self.r_21 <- true; self.s_20 <- State3_18
                     | _ -> self.r_21 <- false )
              | State3_18 ->
                  (if self.r_21 then ());
                  self.x_24.zout <- (~-.) throttle_15;
                  (match self.x_24.zin with
                     | true ->
                         self.nx_23.pos <- 0.;
                         self.r_21 <- true; self.s_20 <- State4_19
                     | _ -> self.r_21 <- false )
              | State4_19 -> (if self.r_21 then ()); self.r_21 <- false );
           (match self.s_20 with
              | State1_16 ->
                  (if self.r_21 then ());
                  self.throttle_15.der <- (/.) (-20.) 14.9
              | State2_17 ->
                  (if self.r_21 then ()); self.throttle_15.der <- 600.
              | State3_18 ->
                  (if self.r_21 then ());
                  self.throttle_15.der <- (/.) ((-.) 58.8235 100.)
                                               ((-.) 50. 15.)
              | State4_19 ->
                  (if self.r_21 then ()); self.throttle_15.der <- 0.
              ); (throttle_15, 0.) in
       cpos_29 := ci_27;
       (if Pervasives.(!) Zls.discrete then
        (((Zls.set (Pervasives.(!) Zls.cvec) !cpos_29 self.nx_23.pos;
           cpos_29 := (+) !cpos_29 1)); ((self.x_24.zin <- false)))
        else (((self.x_24.zin <- Zls.get_zin (Pervasives.(!) Zls.zinvec)
                                             !zpos_30;
                zpos_30 := (+) !zpos_30 1));
              zpos_30 := zi_28;
              ((Zls.set (Pervasives.(!) Zls.zoutvec) !zpos_30 self.x_24.zout;
                zpos_30 := (+) !zpos_30 1));
              ((Zls.set (Pervasives.(!) Zls.dvec) !cpos_29 self.nx_23.der;
                cpos_29 := (+) !cpos_29 1)))); result_31)):float * float) in
  let passing_maneuver_reset self  =
    ((self.r_21 <- false; self.s_20 <- State1_16; self.nx_23.pos <- 60.):
    unit) in
  Hybrid { alloc = passing_maneuver_alloc; step = passing_maneuver_step;
                                           reset = passing_maneuver_reset }
