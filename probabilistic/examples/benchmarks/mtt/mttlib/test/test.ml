(* The Zélus compiler, version 2.0
  (Wed Nov  6 18:58:20 UTC 2019) *)
open Ztypes
open Probzelus
open Mttlib
open Distribution
open Infer_pf
open Util
type _init_fn = unit

let init_fn  = 
   let init_fn_alloc _ = () in let init_fn_copy source dest = () in
  let init_fn_reset self  =
    ((()):unit) in 
  let init_fn_step self ((prob_21:'a4) , (i_20:'a201)) =
    (i_20:'a) in
  Cnode { alloc = init_fn_alloc; copy = init_fn_copy ;
                                 reset = init_fn_reset ; step = init_fn_step }
type ('b , 'a) _model =
  { mutable i_28 : 'b ; mutable t_24 : 'a }

let model  = 
  let Cnode { alloc = i_28_alloc; copy = i_28_copy ;
                                  step = i_28_step ; reset = i_28_reset } = 
  ListP.ini init_fn  in
  let model_alloc _ =
    ();{ t_24 = (42:int);i_28 = i_28_alloc () (* proba *)  } in
  let model_copy source dest =
    dest.t_24 <- source.t_24;i_28_copy source.i_28 dest.i_28 (* proba *) in
  let model_reset self  =
    ((self.t_24 <- 0 ; i_28_reset self.i_28 ):unit) in 
  let model_step self ((prob_22:'a4) , ()) =
    ((let (l_25:int) = self.t_24 in
      self.t_24 <- (+) l_25  1 ;
      (let (ret_23:(int)list) = i_28_step self.i_28 (prob_22 , self.t_24) in
       ret_23)):int list) in
  Cnode { alloc = model_alloc; copy = model_copy ;
                               reset = model_reset ; step = model_step }
type ('a) _main =
  { mutable i_29 : 'a }

let main  = 
  let Cnode { alloc = i_29_alloc; copy = i_29_copy ;
                                  step = i_29_step ; reset = i_29_reset } = 
  Infer_pf.infer 1  model  in
  let main_alloc _ =
    ();{ i_29 = i_29_alloc () (* discrete *)  } in
  let main_copy source dest =
    i_29_copy source.i_29 dest.i_29 (* discrete *) in
  let main_reset self  =
    (i_29_reset self.i_29 :unit) in 
  let main_step self () =
    ((let (lst_distr_27:((int)list)Distribution.t) = i_29_step self.i_29 () in
      let (lst_26:(int)list) = Distribution.draw lst_distr_27 in
      let () = print_string ((^) (Util.string_of_int_list lst_26)  "\n") in
      ()):unit) in
  Cnode { alloc = main_alloc; copy = main_copy ;
                              reset = main_reset ; step = main_step }
