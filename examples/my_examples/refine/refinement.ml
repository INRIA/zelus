(* The Zelus compiler, version 2.1-dev
  (2021-05-19-23:17) *)
open Ztypes
let pi = 3.14159

let w = ( *. ) pi  2.

let y0 = 2.

let y'0 = 0.

type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_25 : 'f ;
    mutable h_34 : 'e ;
    mutable i_32 : 'd ;
    mutable h_30 : 'c ; mutable y'_28 : 'b ; mutable y_27 : 'a }

let main (cstate_38:Ztypes.cstate) = 
  
  let main_alloc _ =
    cstate_38.cmax <- (+) cstate_38.cmax  2;
    { major_25 = false ;
      h_34 = 42. ;
      i_32 = (false:bool) ;
      h_30 = (42.:float) ;
      y'_28 = { pos = 42.; der = 0. } ; y_27 = { pos = 42.; der = 0. } } in
  let main_step self ((time_24:float) , ()) =
    ((let (cindex_39:int) = cstate_38.cindex in
      let cpos_41 = ref (cindex_39:int) in
      cstate_38.cindex <- (+) cstate_38.cindex  2 ;
      self.major_25 <- cstate_38.major ;
      (if cstate_38.major then
       for i_1 = cindex_39 to 1 do Zls.set cstate_38.dvec  i_1  0. done
       else ((self.y'_28.pos <- Zls.get cstate_38.cvec  !cpos_41 ;
              cpos_41 := (+) !cpos_41  1) ;
             (self.y_27.pos <- Zls.get cstate_38.cvec  !cpos_41 ;
              cpos_41 := (+) !cpos_41  1))) ;
      (let (result_43:unit) =
           let h_33 = ref (infinity:float) in
           (if self.i_32 then self.h_30 <- (+.) time_24  0.) ;
           (let (z_31:bool) = (&&) self.major_25  ((>=) time_24  self.h_30) in
            self.h_30 <- (if z_31 then (+.) self.h_30  0.01 else self.h_30) ;
            h_33 := min !h_33  self.h_30 ;
            self.h_34 <- !h_33 ;
            (if self.i_32 then self.y'_28.pos <- y'0) ;
            (if self.i_32 then self.y_27.pos <- y0) ;
            self.i_32 <- false ;
            (let (l_29:float) = self.y_27.pos in
             (begin match z_31 with
                    | true ->
                        let () = print_endline (string_of_float l_29) in
                        () | _ -> ()  end) ;
             self.y'_28.der <- ( *. ) (( *. ) ((~-.) w)  w)  self.y_27.pos ;
             self.y_27.der <- self.y'_28.pos ; ())) in
       cstate_38.horizon <- min cstate_38.horizon  self.h_34 ;
       cpos_41 := cindex_39 ;
       (if cstate_38.major then
        (((Zls.set cstate_38.cvec  !cpos_41  self.y'_28.pos ;
           cpos_41 := (+) !cpos_41  1) ;
          (Zls.set cstate_38.cvec  !cpos_41  self.y_27.pos ;
           cpos_41 := (+) !cpos_41  1)))
        else (((Zls.set cstate_38.dvec  !cpos_41  self.y'_28.der ;
                cpos_41 := (+) !cpos_41  1) ;
               (Zls.set cstate_38.dvec  !cpos_41  self.y_27.der ;
                cpos_41 := (+) !cpos_41  1)))) ; result_43)):unit) in 
  let main_reset self  =
    (self.i_32 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
