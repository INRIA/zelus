(* The Zelus compiler, version 2.1-dev
  (2021-07-28-11:6) *)
open Ztypes
external control_robot_ml: int -> int -> unit = "control_robot_c" 
type state__180 =
Test_StopR_36 | Test_Right_35 | Test_StopL_34 | Test_Left_33 
type state__179 =
Test_StopB_32 | Test_Backward_31 | Test_StopF_30 | Test_Forward_29 
type ('l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_52 : 'l ;
    mutable h_67 : 'k ;
    mutable h_65 : 'j ;
    mutable i_63 : 'i ;
    mutable h_61 : 'h ;
    mutable r_60 : 'g ;
    mutable s_59 : 'f ;
    mutable r_58 : 'e ;
    mutable s_57 : 'd ;
    mutable result_56 : 'c ; mutable vel2_55 : 'b ; mutable vel1_54 : 'a }

let main (cstate_68:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_52 = false ;
      h_67 = 42. ;
      h_65 = (42.:float) ;
      i_63 = (false:bool) ;
      h_61 = (42.:float) ;
      r_60 = (false:bool) ;
      s_59 = (Test_StopR_36:state__180) ;
      r_58 = (false:bool) ;
      s_57 = (Test_StopB_32:state__179) ;
      result_56 = (():unit) ; vel2_55 = (42:int) ; vel1_54 = (42:int) } in
  let main_step self ((time_51:float) , ()) =
    ((self.major_52 <- cstate_68.major ;
      (let (result_73:unit) =
           let h_66 = ref (infinity:float) in
           let encore_64 = ref (false:bool) in
           (if self.i_63 then self.h_61 <- (+.) time_51  0.) ;
           (let (z_62:bool) = (&&) self.major_52  ((>=) time_51  self.h_61) in
            let (trigger_53:zero) = z_62 in
            (begin match self.s_59 with
                   | Test_Left_33 ->
                       (if self.r_60 then ()) ;
                       self.vel2_55 <- 55 ;
                       (begin match trigger_53 with
                              | true ->
                                  encore_64 := true ;
                                  self.r_60 <- true ;
                                  self.s_59 <- Test_StopL_34
                              | _ -> self.r_60 <- false  end)
                   | Test_StopL_34 ->
                       (if self.r_60 then ()) ;
                       self.vel2_55 <- 0 ;
                       (begin match trigger_53 with
                              | true ->
                                  encore_64 := true ;
                                  self.r_60 <- true ;
                                  self.s_59 <- Test_Right_35
                              | _ -> self.r_60 <- false  end)
                   | Test_Right_35 ->
                       (if self.r_60 then ()) ;
                       self.vel2_55 <- (-55) ;
                       (begin match trigger_53 with
                              | true ->
                                  encore_64 := true ;
                                  self.r_60 <- true ;
                                  self.s_59 <- Test_StopR_36
                              | _ -> self.r_60 <- false  end)
                   | Test_StopR_36 ->
                       (if self.r_60 then ()) ;
                       self.vel2_55 <- 0 ;
                       (begin match trigger_53 with
                              | true ->
                                  encore_64 := true ;
                                  self.r_60 <- true ;
                                  self.s_59 <- Test_Left_33
                              | _ -> self.r_60 <- false  end)
                    end) ;
            (begin match self.s_57 with
                   | Test_Forward_29 ->
                       (if self.r_58 then ()) ;
                       self.vel1_54 <- 30 ;
                       (begin match trigger_53 with
                              | true ->
                                  encore_64 := true ;
                                  self.r_58 <- true ;
                                  self.s_57 <- Test_StopF_30
                              | _ -> self.r_58 <- false  end)
                   | Test_StopF_30 ->
                       (if self.r_58 then ()) ;
                       self.vel1_54 <- 0 ;
                       (begin match trigger_53 with
                              | true ->
                                  encore_64 := true ;
                                  self.r_58 <- true ;
                                  self.s_57 <- Test_Backward_31
                              | _ -> self.r_58 <- false  end)
                   | Test_Backward_31 ->
                       (if self.r_58 then ()) ;
                       self.vel1_54 <- (-30) ;
                       (begin match trigger_53 with
                              | true ->
                                  encore_64 := true ;
                                  self.r_58 <- true ;
                                  self.s_57 <- Test_StopB_32
                              | _ -> self.r_58 <- false  end)
                   | Test_StopB_32 ->
                       (if self.r_58 then ()) ;
                       self.vel1_54 <- 0 ;
                       (begin match trigger_53 with
                              | true ->
                                  encore_64 := true ;
                                  self.r_58 <- true ;
                                  self.s_57 <- Test_Forward_29
                              | _ -> self.r_58 <- false  end)
                    end) ;
            self.h_65 <- (if !encore_64 then 0. else infinity) ;
            self.h_61 <- (if z_62 then (+.) self.h_61  1. else self.h_61) ;
            h_66 := min !h_66  (min self.h_65  self.h_61) ;
            self.h_67 <- !h_66 ;
            self.i_63 <- false ;
            (begin match trigger_53 with
                   | true ->
                       let _ = print_int self.vel1_54 in
                       let _ = print_int self.vel2_55 in
                       let _ = print_newline () in
                       self.result_56 <- (control_robot_ml self.vel1_54 self.vel2_55)
                   | _ -> self.result_56 <- ()  end) ;
            (let () = self.result_56 in
             ())) in
       cstate_68.horizon <- min cstate_68.horizon  self.h_67 ; result_73)):
    unit) in 
  let main_reset self  =
    ((self.r_60 <- false ;
      self.s_59 <- Test_Left_33 ;
      self.i_63 <- true ; self.r_58 <- false ; self.s_57 <- Test_Forward_29):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
