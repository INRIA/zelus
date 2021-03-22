(* The Zelus compiler, version 2.1-dev
  (2021-03-22-1:40) *)
open Ztypes
let pi = 3.14159

let w = ( *. ) pi  2.

let y0 = 1.

let y'0 = 0.

type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_22 : 'e ;
    mutable i_28 : 'd ;
    mutable x_27 : 'c ; mutable y'_25 : 'b ; mutable y_24 : 'a }

let main (cstate_32:Ztypes.cstate) = 
  
  let main_alloc _ =
    cstate_32.cmax <- (+) cstate_32.cmax  2 ;
    cstate_32.zmax <- (+) cstate_32.zmax  1;
    { major_22 = false ;
      i_28 = (false:bool) ;
      x_27 = { zin = false; zout = 1. } ;
      y'_25 = { pos = 42.; der = 0. } ; y_24 = { pos = 42.; der = 0. } } in
  let main_step self ((time_21:float) , ()) =
    ((let (cindex_33:int) = cstate_32.cindex in
      let cpos_35 = ref (cindex_33:int) in
      let (zindex_34:int) = cstate_32.zindex in
      let zpos_36 = ref (zindex_34:int) in
      cstate_32.cindex <- (+) cstate_32.cindex  2 ;
      cstate_32.zindex <- (+) cstate_32.zindex  1 ;
      self.major_22 <- cstate_32.major ;
      (if cstate_32.major then
       for i_1 = cindex_33 to 1 do Zls.set cstate_32.dvec  i_1  0. done
       else ((self.y'_25.pos <- Zls.get cstate_32.cvec  !cpos_35 ;
              cpos_35 := (+) !cpos_35  1) ;
             (self.y_24.pos <- Zls.get cstate_32.cvec  !cpos_35 ;
              cpos_35 := (+) !cpos_35  1))) ;
      (let (result_37:unit) =
           (if self.i_28 then self.y'_25.pos <- y'0) ;
           (if self.i_28 then self.y_24.pos <- y0) ;
           self.i_28 <- false ;
           (let (l_26:float) = self.y_24.pos in
            (begin match self.x_27.zin with
                   | true ->
                       let () = print_endline (string_of_float l_26) in
                       () | _ -> ()  end) ;
            self.x_27.zout <- self.y_24.pos ;
            self.y'_25.der <- ( *. ) (( *. ) ((~-.) w)  w)  self.y_24.pos ;
            self.y_24.der <- self.y'_25.pos ; ()) in
       cpos_35 := cindex_33 ;
       (if cstate_32.major then
        (((Zls.set cstate_32.cvec  !cpos_35  self.y'_25.pos ;
           cpos_35 := (+) !cpos_35  1) ;
          (Zls.set cstate_32.cvec  !cpos_35  self.y_24.pos ;
           cpos_35 := (+) !cpos_35  1)) ; ((self.x_27.zin <- false)))
        else (((self.x_27.zin <- Zls.get_zin cstate_32.zinvec  !zpos_36 ;
                zpos_36 := (+) !zpos_36  1)) ;
              zpos_36 := zindex_34 ;
              ((Zls.set cstate_32.zoutvec  !zpos_36  self.x_27.zout ;
                zpos_36 := (+) !zpos_36  1)) ;
              ((Zls.set cstate_32.dvec  !cpos_35  self.y'_25.der ;
                cpos_35 := (+) !cpos_35  1) ;
               (Zls.set cstate_32.dvec  !cpos_35  self.y_24.der ;
                cpos_35 := (+) !cpos_35  1)))) ; result_37)):unit) in 
  let main_reset self  =
    (self.i_28 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
