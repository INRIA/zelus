(* The Zelus compiler, version 2.1-dev
  (2022-02-19-7:52) *)
open Ztypes
let ground (x_53:float) =
  Flatworld.ground x_53

let ground_abs (x_54:float) =
  Flatworld.ground_abs x_54

let x_0 = 5.

let y_0 = 10.

let g = 9.81

let loose = 0.8

type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _ball =
  { mutable major_58 : 'g ;
    mutable h_68 : 'f ;
    mutable h_66 : 'e ;
    mutable i_64 : 'd ;
    mutable x_63 : 'c ; mutable y_v_60 : 'b ; mutable y_59 : 'a }

let ball (cstate_84:Ztypes.cstate) = 
  
  let ball_alloc _ =
    cstate_84.cmax <- (+) cstate_84.cmax  2 ;
    cstate_84.zmax <- (+) cstate_84.zmax  1;
    { major_58 = false ;
      h_68 = 42. ;
      h_66 = (42.:float) ;
      i_64 = (false:bool) ;
      x_63 = { zin = false; zout = 1. } ;
      y_v_60 = { pos = 42.; der = 0. } ; y_59 = { pos = 42.; der = 0. } } in
  let ball_step self ((time_57:float) , ((x_55:float) , (y_0_56:float))) =
    ((let (cindex_85:int) = cstate_84.cindex in
      let cpos_87 = ref (cindex_85:int) in
      let (zindex_86:int) = cstate_84.zindex in
      let zpos_88 = ref (zindex_86:int) in
      cstate_84.cindex <- (+) cstate_84.cindex  2 ;
      cstate_84.zindex <- (+) cstate_84.zindex  1 ;
      self.major_58 <- cstate_84.major ;
      (if cstate_84.major then
       for i_1 = cindex_85 to 1 do Zls.set cstate_84.dvec  i_1  0. done
       else ((self.y_v_60.pos <- Zls.get cstate_84.cvec  !cpos_87 ;
              cpos_87 := (+) !cpos_87  1) ;
             (self.y_59.pos <- Zls.get cstate_84.cvec  !cpos_87 ;
              cpos_87 := (+) !cpos_87  1))) ;
      (let (result_89:(float  * float  * zero)) =
           let h_67 = ref (infinity:float) in
           let encore_65 = ref (false:bool) in
           let (l_62:float) = self.y_v_60.pos in
           (begin match self.x_63.zin with
                  | true ->
                      encore_65 := true ;
                      self.y_v_60.pos <- ( *. ) ((~-.) loose)  l_62
                  | _ -> ()  end) ;
           self.h_66 <- (if !encore_65 then 0. else infinity) ;
           h_67 := min !h_67  self.h_66 ;
           self.h_68 <- !h_67 ;
           (if self.i_64 then self.y_59.pos <- y_0_56) ;
           self.i_64 <- false ;
           self.x_63.zout <- (-.) (ground x_55)  self.y_59.pos ;
           self.y_v_60.der <- (~-.) g ;
           self.y_59.der <- self.y_v_60.pos ;
           (self.y_59.pos , self.y_v_60.pos , self.x_63.zin) in
       cstate_84.horizon <- min cstate_84.horizon  self.h_68 ;
       cpos_87 := cindex_85 ;
       (if cstate_84.major then
        (((Zls.set cstate_84.cvec  !cpos_87  self.y_v_60.pos ;
           cpos_87 := (+) !cpos_87  1) ;
          (Zls.set cstate_84.cvec  !cpos_87  self.y_59.pos ;
           cpos_87 := (+) !cpos_87  1)) ; ((self.x_63.zin <- false)))
        else (((self.x_63.zin <- Zls.get_zin cstate_84.zinvec  !zpos_88 ;
                zpos_88 := (+) !zpos_88  1)) ;
              zpos_88 := zindex_86 ;
              ((Zls.set cstate_84.zoutvec  !zpos_88  self.x_63.zout ;
                zpos_88 := (+) !zpos_88  1)) ;
              ((Zls.set cstate_84.dvec  !cpos_87  self.y_v_60.der ;
                cpos_87 := (+) !cpos_87  1) ;
               (Zls.set cstate_84.dvec  !cpos_87  self.y_59.der ;
                cpos_87 := (+) !cpos_87  1)))) ; result_89)):float *
                                                             float * zero) in
  
  let ball_reset self  =
    ((self.y_v_60.pos <- 0. ; self.i_64 <- true):unit) in
  Node { alloc = ball_alloc; step = ball_step ; reset = ball_reset }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_83 : 'g ;
    mutable major_70 : 'f ;
    mutable h_79 : 'e ;
    mutable i_77 : 'd ;
    mutable h_75 : 'c ; mutable i_82 : 'b ; mutable m_80 : 'a }

let main (cstate_90:Ztypes.cstate) = 
  let Node { alloc = i_83_alloc; step = i_83_step ; reset = i_83_reset } = ball 
  cstate_90 in
  let main_alloc _ =
    ();
    { major_70 = false ;
      h_79 = 42. ;
      i_77 = (false:bool) ;
      h_75 = (42.:float) ; i_82 = (false:bool) ; m_80 = (42.:float);
      i_83 = i_83_alloc () (* continuous *)  } in
  let main_step self ((time_69:float) , ()) =
    ((self.major_70 <- cstate_90.major ;
      (let (result_95:unit) =
           let h_78 = ref (infinity:float) in
           let resultv_73 = ref (():unit) in
           (if self.i_77 then self.h_75 <- (+.) time_69  0.) ;
           (let (z_76:bool) = (&&) self.major_70  ((>=) time_69  self.h_75) in
            self.h_75 <- (if z_76 then (+.) self.h_75  0.04 else self.h_75) ;
            h_78 := min !h_78  self.h_75 ;
            self.h_79 <- !h_78 ;
            self.i_77 <- false ;
            (let ((y_71:float) , _ , (z_72:zero)) =
                 i_83_step self.i_83 (time_69 , (x_0 , y_0)) in
             (begin match (z_72 , z_76) with
                    | (_ , true) | (true , _) ->
                        (if self.i_82 then self.m_80 <- y_71) ;
                        self.i_82 <- false ;
                        (let (x_81:float) = self.m_80 in
                         self.m_80 <- y_71 ;
                         resultv_73 := Showball.show x_0  x_81  x_0  y_71)
                    | _ -> ()  end) ; ())) in
       cstate_90.horizon <- min cstate_90.horizon  self.h_79 ; result_95)):
    unit) in 
  let main_reset self  =
    ((self.i_77 <- true ; i_83_reset self.i_83  ; self.i_82 <- true):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
