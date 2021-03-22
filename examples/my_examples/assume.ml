(* The Zelus compiler, version 2.1-dev
  (2021-03-22-1:40) *)
open Ztypes
let pi = 3.14159

let w = ( *. ) pi  2.

let y0 = 1.

let y'0 = 0.

type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_28 : 'f ;
    mutable h_38 : 'e ;
    mutable i_36 : 'd ;
    mutable h_34 : 'c ; mutable y'_32 : 'b ; mutable y_31 : 'a }

let main (cstate_42:Ztypes.cstate) = 
  
  let main_alloc _ =
    cstate_42.cmax <- (+) cstate_42.cmax  2;
    { major_28 = false ;
      h_38 = 42. ;
      i_36 = (false:bool) ;
      h_34 = (42.:float) ;
      y'_32 = { pos = 42.; der = 0. } ; y_31 = { pos = 42.; der = 0. } } in
  let main_step self ((time_27:float) , ()) =
    ((let (cindex_43:int) = cstate_42.cindex in
      let cpos_45 = ref (cindex_43:int) in
      cstate_42.cindex <- (+) cstate_42.cindex  2 ;
      self.major_28 <- cstate_42.major ;
      (if cstate_42.major then
       for i_1 = cindex_43 to 1 do Zls.set cstate_42.dvec  i_1  0. done
       else ((self.y'_32.pos <- Zls.get cstate_42.cvec  !cpos_45 ;
              cpos_45 := (+) !cpos_45  1) ;
             (self.y_31.pos <- Zls.get cstate_42.cvec  !cpos_45 ;
              cpos_45 := (+) !cpos_45  1))) ;
      (let (result_47:unit) =
           let h_37 = ref (infinity:float) in
           (if self.i_36 then self.h_34 <- (+.) time_27  0.) ;
           (let (z_35:bool) = (&&) self.major_28  ((>=) time_27  self.h_34) in
            self.h_34 <- (if z_35 then (+.) self.h_34  0.01 else self.h_34) ;
            h_37 := min !h_37  self.h_34 ;
            self.h_38 <- !h_37 ;
            (if self.i_36 then self.y'_32.pos <- y'0) ;
            (if self.i_36 then self.y_31.pos <- y0) ;
            self.i_36 <- false ;
            (let (l_33:float) = self.y_31.pos in
             (begin match z_35 with
                    | true ->
                        let () = print_endline (string_of_float l_33) in
                        () | _ -> ()  end) ;
             self.y'_32.der <- ( *. ) (( *. ) ((~-.) w)  w)  self.y_31.pos ;
             self.y_31.der <- self.y'_32.pos ; ())) in
       cstate_42.horizon <- min cstate_42.horizon  self.h_38 ;
       cpos_45 := cindex_43 ;
       (if cstate_42.major then
        (((Zls.set cstate_42.cvec  !cpos_45  self.y'_32.pos ;
           cpos_45 := (+) !cpos_45  1) ;
          (Zls.set cstate_42.cvec  !cpos_45  self.y_31.pos ;
           cpos_45 := (+) !cpos_45  1)))
        else (((Zls.set cstate_42.dvec  !cpos_45  self.y'_32.der ;
                cpos_45 := (+) !cpos_45  1) ;
               (Zls.set cstate_42.dvec  !cpos_45  self.y_31.der ;
                cpos_45 := (+) !cpos_45  1)))) ; result_47)):unit) in 
  let main_reset self  =
    (self.i_36 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
