(* The Zelus compiler, version 2.1-dev
  (2022-02-19-7:39) *)
open Ztypes
let ground (x_68:float) =
  World.ground x_68

let ground_abs (x_69:float) =
  World.ground_abs x_69

let x_0 = 0.

let y_0 = 8.

let x_v = 0.72

let g = 9.81

let loose = 0.8

type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _ball =
  { mutable major_73 : 'g ;
    mutable h_83 : 'f ;
    mutable h_81 : 'e ;
    mutable i_79 : 'd ;
    mutable x_78 : 'c ; mutable y_v_75 : 'b ; mutable y_74 : 'a }

let ball (cstate_106:Ztypes.cstate) = 
  
  let ball_alloc _ =
    cstate_106.cmax <- (+) cstate_106.cmax  2 ;
    cstate_106.zmax <- (+) cstate_106.zmax  1;
    { major_73 = false ;
      h_83 = 42. ;
      h_81 = (42.:float) ;
      i_79 = (false:bool) ;
      x_78 = { zin = false; zout = 1. } ;
      y_v_75 = { pos = 42.; der = 0. } ; y_74 = { pos = 42.; der = 0. } } in
  let ball_step self ((time_72:float) , ((x_70:float) , (y_0_71:float))) =
    ((let (cindex_107:int) = cstate_106.cindex in
      let cpos_109 = ref (cindex_107:int) in
      let (zindex_108:int) = cstate_106.zindex in
      let zpos_110 = ref (zindex_108:int) in
      cstate_106.cindex <- (+) cstate_106.cindex  2 ;
      cstate_106.zindex <- (+) cstate_106.zindex  1 ;
      self.major_73 <- cstate_106.major ;
      (if cstate_106.major then
       for i_1 = cindex_107 to 1 do Zls.set cstate_106.dvec  i_1  0. done
       else ((self.y_v_75.pos <- Zls.get cstate_106.cvec  !cpos_109 ;
              cpos_109 := (+) !cpos_109  1) ;
             (self.y_74.pos <- Zls.get cstate_106.cvec  !cpos_109 ;
              cpos_109 := (+) !cpos_109  1))) ;
      (let (result_111:(float  * float  * zero)) =
           let h_82 = ref (infinity:float) in
           let encore_80 = ref (false:bool) in
           let (z_76:zero) = self.x_78.zin in
           let (l_77:float) = self.y_v_75.pos in
           (begin match z_76 with
                  | true ->
                      encore_80 := true ;
                      self.y_v_75.pos <- ( *. ) ((~-.) loose)  l_77
                  | _ -> ()  end) ;
           self.h_81 <- (if !encore_80 then 0. else infinity) ;
           h_82 := min !h_82  self.h_81 ;
           self.h_83 <- !h_82 ;
           (if self.i_79 then self.y_74.pos <- y_0_71) ;
           self.i_79 <- false ;
           self.x_78.zout <- (-.) (ground x_70)  self.y_74.pos ;
           self.y_v_75.der <- (~-.) g ;
           self.y_74.der <- self.y_v_75.pos ;
           (self.y_74.pos , self.y_v_75.pos , z_76) in
       cstate_106.horizon <- min cstate_106.horizon  self.h_83 ;
       cpos_109 := cindex_107 ;
       (if cstate_106.major then
        (((Zls.set cstate_106.cvec  !cpos_109  self.y_v_75.pos ;
           cpos_109 := (+) !cpos_109  1) ;
          (Zls.set cstate_106.cvec  !cpos_109  self.y_74.pos ;
           cpos_109 := (+) !cpos_109  1)) ; ((self.x_78.zin <- false)))
        else (((self.x_78.zin <- Zls.get_zin cstate_106.zinvec  !zpos_110 ;
                zpos_110 := (+) !zpos_110  1)) ;
              zpos_110 := zindex_108 ;
              ((Zls.set cstate_106.zoutvec  !zpos_110  self.x_78.zout ;
                zpos_110 := (+) !zpos_110  1)) ;
              ((Zls.set cstate_106.dvec  !cpos_109  self.y_v_75.der ;
                cpos_109 := (+) !cpos_109  1) ;
               (Zls.set cstate_106.dvec  !cpos_109  self.y_74.der ;
                cpos_109 := (+) !cpos_109  1)))) ; result_111)):float *
                                                                float * zero) in
  
  let ball_reset self  =
    ((self.y_v_75.pos <- 0. ; self.i_79 <- true):unit) in
  Node { alloc = ball_alloc; step = ball_step ; reset = ball_reset }
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_105 : 'i ;
    mutable major_85 : 'h ;
    mutable h_99 : 'g ;
    mutable i_97 : 'f ;
    mutable h_95 : 'e ;
    mutable x_86 : 'd ;
    mutable i_104 : 'c ; mutable m_102 : 'b ; mutable m_100 : 'a }

let main (cstate_112:Ztypes.cstate) = 
  let Node { alloc = i_105_alloc; step = i_105_step ; reset = i_105_reset } = ball 
  cstate_112 in
  let main_alloc _ =
    cstate_112.cmax <- (+) cstate_112.cmax  1;
    { major_85 = false ;
      h_99 = 42. ;
      i_97 = (false:bool) ;
      h_95 = (42.:float) ;
      x_86 = { pos = 42.; der = 0. } ;
      i_104 = (false:bool) ; m_102 = (42.:float) ; m_100 = (42.:float);
      i_105 = i_105_alloc () (* continuous *)  } in
  let main_step self ((time_84:float) , ()) =
    ((let (cindex_113:int) = cstate_112.cindex in
      let cpos_115 = ref (cindex_113:int) in
      cstate_112.cindex <- (+) cstate_112.cindex  1 ;
      self.major_85 <- cstate_112.major ;
      (if cstate_112.major then
       for i_1 = cindex_113 to 0 do Zls.set cstate_112.dvec  i_1  0. done
       else ((self.x_86.pos <- Zls.get cstate_112.cvec  !cpos_115 ;
              cpos_115 := (+) !cpos_115  1))) ;
      (let (result_117:unit) =
           let h_98 = ref (infinity:float) in
           let resultp_94 = ref (false:bool) in
           let resultv_93 = ref (():unit) in
           let resultp_92 = ref (false:bool) in
           let resultv_91 = ref (():unit) in
           let okp_90 = ref (false:bool) in
           (if self.i_97 then self.h_95 <- (+.) time_84  0.) ;
           (let (z_96:bool) = (&&) self.major_85  ((>=) time_84  self.h_95) in
            self.h_95 <- (if z_96 then (+.) self.h_95  0.04 else self.h_95) ;
            h_98 := min !h_98  self.h_95 ;
            self.h_99 <- !h_98 ;
            (if self.i_97 then self.x_86.pos <- x_0) ;
            self.i_97 <- false ;
            self.x_86.der <- x_v ;
            (let ((y_87:float) , _ , (z_88:zero)) =
                 i_105_step self.i_105 (time_84 , (self.x_86.pos , y_0)) in
             (begin match (z_88 , z_96) with
                    | (_ , true) -> resultp_92 := true ; resultv_91 := ()
                    | (true , _) -> resultp_92 := true ; resultv_91 := ()
                    | _ -> ()  end) ;
             (let (okv_89:unit) = !resultv_91 in
              okp_90 := !resultp_92 ;
              (begin match (okv_89 , !okp_90) with
                     | (() , true) ->
                         (if self.i_104 then self.m_102 <- y_87) ;
                         (if self.i_104 then self.m_100 <- self.x_86.pos) ;
                         self.i_104 <- false ;
                         resultp_94 := true ;
                         (let (x_103:float) = self.m_102 in
                          self.m_102 <- y_87 ;
                          (let (x_101:float) = self.m_100 in
                           self.m_100 <- self.x_86.pos ;
                           resultv_93 := Showball.show x_101 
                                                       x_103 
                                                       self.x_86.pos  y_87))
                     | _ -> ()  end) ;
              (let _ = (!resultv_93 , !resultp_94) in
               ())))) in
       cstate_112.horizon <- min cstate_112.horizon  self.h_99 ;
       cpos_115 := cindex_113 ;
       (if cstate_112.major then
        (((Zls.set cstate_112.cvec  !cpos_115  self.x_86.pos ;
           cpos_115 := (+) !cpos_115  1)))
        else (((Zls.set cstate_112.dvec  !cpos_115  self.x_86.der ;
                cpos_115 := (+) !cpos_115  1)))) ; result_117)):unit) in 
  let main_reset self  =
    ((self.i_97 <- true ; i_105_reset self.i_105  ; self.i_104 <- true):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
