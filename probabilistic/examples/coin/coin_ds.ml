(* The Zélus compiler, version 2.0
  (Mon Oct 14 11:01:30 EDT 2019) *)
open Ztypes
type state__887 = Coin_ds_Stop_71 | Coin_ds_Run_70 
type state__886 = Coin_ds_Cheater_55 | Coin_ds_Observe_54 
open Probzelus
open Distribution
open Infer_ds_gc_copy
type ('d , 'c , 'b , 'a) _coin =
  { mutable i_112 : 'd ;
    mutable i_111 : 'c ; mutable i_84 : 'b ; mutable xt_83 : 'a }

let coin  = 
  let Cnode { alloc = i_112_alloc; copy = i_112_copy ;
                                   step = i_112_step ; reset = i_112_reset } = Infer_ds_gc_copy.sample 
   in 
  let Cnode { alloc = i_111_alloc; copy = i_111_copy ;
                                   step = i_111_step ; reset = i_111_reset } = Infer_ds_gc_copy.observe 
   in
  let coin_alloc _ =
    ();
    { i_84 = (false:bool) ;
      xt_83 = (Obj.magic ():float Infer_ds_gc_copy.expr);
      i_112 = i_112_alloc () (* proba *)  ;
      i_111 = i_111_alloc () (* proba *)  } in
  let coin_copy source dest =
    dest.i_84 <- source.i_84 ; dest.xt_83 <- source.xt_83;
    i_112_copy source.i_112 dest.i_112 (* proba *) ;
    i_111_copy source.i_111 dest.i_111 (* proba *) in
  let coin_reset self  =
    ((self.i_84 <- true ; i_112_reset self.i_112  ; i_111_reset self.i_111 ):
    unit) in 
  let coin_step self ((prob_82:'a4) , (yobs_81:bool)) =
    (((if self.i_84 then
       (self.xt_83 <- i_112_step self.i_112
                        (prob_82 , (Infer_ds_gc_copy.beta (1. , 1.))) ;
        i_112_reset self.i_112 )) ;
      self.i_84 <- false ;
      (let () =
           i_111_step self.i_111
             (prob_82 , ((Infer_ds_gc_copy.bernoulli self.xt_83) , yobs_81)) in
       self.xt_83)):float Infer_ds_gc_copy.expr) in
  Cnode { alloc = coin_alloc; copy = coin_copy ;
                              reset = coin_reset ; step = coin_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _cheater_detector =
  { mutable i_113 : 'g ;
    mutable r_90 : 'f ;
    mutable s_89 : 'e ;
    mutable cheating_88 : 'd ;
    mutable m_87 : 'c ; mutable cheater_86 : 'b ; mutable theta_dist_91 : 'a }

let cheater_detector  = 
  let Cnode { alloc = i_113_alloc; copy = i_113_copy ;
                                   step = i_113_step ; reset = i_113_reset } = 
  Infer_ds_gc_copy.infer 1000  coin  in
  let cheater_detector_alloc _ =
    ();
    { r_90 = (false:bool) ;
      s_89 = (Coin_ds_Cheater_55:state__886) ;
      cheating_88 = (42.:float) ;
      m_87 = (42.:float) ;
      cheater_86 = (false:bool) ;
      theta_dist_91 = (Obj.magic ():float Distribution.t);
      i_113 = i_113_alloc () (* discrete *)  } in
  let cheater_detector_copy source dest =
    dest.r_90 <- source.r_90 ;
    dest.s_89 <- source.s_89 ;
    dest.cheating_88 <- source.cheating_88 ;
    dest.m_87 <- source.m_87 ;
    dest.cheater_86 <- source.cheater_86 ;
    dest.theta_dist_91 <- source.theta_dist_91;
    i_113_copy source.i_113 dest.i_113 (* discrete *) in
  let cheater_detector_reset self  =
    ((self.r_90 <- false ;
      self.s_89 <- Coin_ds_Observe_54 ; i_113_reset self.i_113 ):unit) in 
  let cheater_detector_step self (flip_85:bool) =
    (((begin match self.s_89 with
             | Coin_ds_Observe_54 ->
                 (if self.r_90 then i_113_reset self.i_113 ) ;
                 self.cheater_86 <- false ;
                 self.theta_dist_91 <- i_113_step self.i_113 flip_85 ;
                 (let ((copy_109:float) , (copy_110:float)) =
                      Distribution.stats_float self.theta_dist_91 in
                  let _ = print_string ((^) "("  ((^) "theta"  ": mean =  ")) in
                  let _ = print_float copy_109 in
                  let _ = print_string " std = " in
                  let _ = print_float copy_110 in
                  let _ = print_string ")" in
                  let () = print_newline () in
                  self.m_87 <- Distribution.mean_float self.theta_dist_91 ;
                  (begin match (&&) false 
                                    ((||) ((<) self.m_87  0.25) 
                                          ((>) self.m_87  0.75)) with
                         | true ->
                             self.cheating_88 <- self.m_87 ;
                             self.r_90 <- true ;
                             self.s_89 <- Coin_ds_Cheater_55
                         | _ -> self.r_90 <- false  end))
             | Coin_ds_Cheater_55 ->
                 (if self.r_90 then ()) ;
                 self.m_87 <- self.cheating_88 ;
                 self.cheater_86 <- true ; self.r_90 <- false
              end) ; (self.cheater_86 , self.m_87)):bool * float) in
  Cnode { alloc = cheater_detector_alloc; copy = cheater_detector_copy ;
                                          reset = cheater_detector_reset ;
                                          step = cheater_detector_step }
type ('a) _flips =
  { mutable m_98 : 'a }

let flips  = 
   let flips_alloc _ =
     ();{ m_98 = (42:int) } in
  let flips_copy source dest =
    dest.m_98 <- source.m_98 in
  let flips_reset self  =
    (self.m_98 <- 0:unit) in 
  let flips_step self ((nb_true_95:int) , (n_94:int)) =
    ((let (x_99:int) = self.m_98 in
      let (cpt_97:int) = (mod) ((+) x_99  1)  n_94 in
      let (b_96:bool) = (<) cpt_97  nb_true_95 in
      self.m_98 <- cpt_97 ; b_96):bool) in
  Cnode { alloc = flips_alloc; copy = flips_copy ;
                               reset = flips_reset ; step = flips_step }
type _print_bool = unit

let print_bool  = 
   let print_bool_alloc _ = () in let print_bool_copy source dest = () in
  let print_bool_reset self  =
    ((()):unit) in 
  let print_bool_step self (b_100:bool) =
    ((let (s_101:string) = if b_100 then "true " else "false" in
      print_string s_101):unit) in
  Cnode { alloc = print_bool_alloc; copy = print_bool_copy ;
                                    reset = print_bool_reset ;
                                    step = print_bool_step }
let random_init = Random.self_init ()

type ('d , 'c , 'b , 'a) _main_ds =
  { mutable i_114 : 'd ;
    mutable r_108 : 'c ; mutable s_107 : 'b ; mutable dummy_104 : 'a }

let main_ds  = 
  let Cnode { alloc = i_114_alloc; copy = i_114_copy ;
                                   step = i_114_step ; reset = i_114_reset } = cheater_detector 
   in
  let main_ds_alloc _ =
    ();
    { r_108 = (false:bool) ;
      s_107 = (Coin_ds_Stop_71:state__887) ; dummy_104 = (():unit);
      i_114 = i_114_alloc () (* discrete *)  } in
  let main_ds_copy source dest =
    dest.r_108 <- source.r_108 ;
    dest.s_107 <- source.s_107 ; dest.dummy_104 <- source.dummy_104;
    i_114_copy source.i_114 dest.i_114 (* discrete *) in
  let main_ds_reset self  =
    ((self.r_108 <- false ;
      self.s_107 <- Coin_ds_Run_70 ;
      self.dummy_104 <- () ; i_114_reset self.i_114 ):unit) in 
  let main_ds_step self () =
    ((let (b_102:bool) = Distribution.draw (Distribution.bernoulli 0.2) in
      let ((cheater_103:bool) , (m_105:float)) = i_114_step self.i_114 b_102 in
      (begin match self.s_107 with
             | Coin_ds_Run_70 ->
                 (if self.r_108 then ()) ;
                 (begin match cheater_103 with
                        | true ->
                            self.dummy_104 <- print_endline "Cheating!!!" ;
                            self.r_108 <- true ;
                            self.s_107 <- Coin_ds_Stop_71
                        | _ -> self.r_108 <- false  end)
             | Coin_ds_Stop_71 ->
                 (if self.r_108 then ()) ; self.r_108 <- false
              end) ; ()):unit) in
  Cnode { alloc = main_ds_alloc; copy = main_ds_copy ;
                                 reset = main_ds_reset ; step = main_ds_step }
