(* The Zélus compiler, version 2.0
  (Wed Nov  6 18:58:20 UTC 2019) *)
open Ztypes
open Probzelus
open Util
open Distribution
open Zelus_owl
open Infer_pf
let position ((tr_num_66:'a744) , (tr_65:Mat.mat)) =
  (tr_num_66 , (Util.( *@ ) Util.proj_pos  tr_65))

type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _metrics =
  { mutable i_107 : 'g ;
    mutable i_100 : 'f ;
    mutable tr_match_92 : 'e ;
    mutable agg_mme_75 : 'd ;
    mutable agg_m_74 : 'c ; mutable agg_g_73 : 'b ; mutable agg_fp_72 : 'a }

let metrics  = 
  let Cnode { alloc = i_107_alloc; copy = i_107_copy ;
                                   step = i_107_step ; reset = i_107_reset } = Infer_pf.sample 
   in
  let metrics_alloc _ =
    ();
    { i_100 = (false:bool) ;
      tr_match_92 = (Obj.magic ():Util.tr_map) ;
      agg_mme_75 = (42:int) ;
      agg_m_74 = (42:int) ; agg_g_73 = (42:int) ; agg_fp_72 = (42:int);
      i_107 = i_107_alloc () (* proba *)  } in
  let metrics_copy source dest =
    dest.i_100 <- source.i_100 ;
    dest.tr_match_92 <- source.tr_match_92 ;
    dest.agg_mme_75 <- source.agg_mme_75 ;
    dest.agg_m_74 <- source.agg_m_74 ;
    dest.agg_g_73 <- source.agg_g_73 ; dest.agg_fp_72 <- source.agg_fp_72;
    i_107_copy source.i_107 dest.i_107 (* proba *) in
  let metrics_reset self  =
    ((i_107_reset self.i_107  ;
      self.i_100 <- true ;
      self.agg_g_73 <- 0 ;
      self.agg_mme_75 <- 0 ; self.agg_m_74 <- 0 ; self.agg_fp_72 <- 0):
    unit) in 
  let metrics_step self ((prob_69:'a4) ,
                         ((true_tr_68:((int  * Mat.mat))list) ,
                          (tr_dist_67:(((int  * Mat.mat))list)Distribution.t))) =
    ((let (est_tr_79:((int  * Mat.mat))list) =
          i_107_step self.i_107 (prob_69 , tr_dist_67) in
      let (est_tr_pos_80:((int  * Mat.mat))list) =
          List.map position  est_tr_79 in
      (if self.i_100 then self.tr_match_92 <- Util.empty_matching) ;
      (let (l_99:Util.tr_map) = self.tr_match_92 in
       let ((_ ,
             _ ,
             (metrics_86:int) ,
             (metrics_87:int) , (metrics_88:int) , (metrics_89:int)) ,
            (copy_106:Util.tr_map)) =
           Util.matching l_99  true_tr_68  est_tr_pos_80 in
       self.tr_match_92 <- copy_106 ;
       self.i_100 <- false ;
       (let (l_96:int) = self.agg_g_73 in
        self.agg_g_73 <- (+) l_96  metrics_89 ;
        (let (l_98:int) = self.agg_mme_75 in
         self.agg_mme_75 <- (+) l_98  metrics_88 ;
         (let (l_97:int) = self.agg_m_74 in
          self.agg_m_74 <- (+) l_97  metrics_87 ;
          (let (l_95:int) = self.agg_fp_72 in
           self.agg_fp_72 <- (+) l_95  metrics_86 ;
           (let (one_minus_mota_91:float) =
                (/.) (float_of_int ((+) ((+) self.agg_fp_72  self.agg_m_74) 
                                        self.agg_mme_75)) 
                     (float_of_int self.agg_g_73) in
            let (err_78:float) =
                if (>=) one_minus_mota_91  1.
                then infinity
                else (-.) ((/.) 1.  ((-.) 1.  one_minus_mota_91))  1. in
            err_78))))))):float) in
  Cnode { alloc = metrics_alloc; copy = metrics_copy ;
                                 reset = metrics_reset ; step = metrics_step }
type ('a) _main =
  { mutable i_108 : 'a }

let main (particles_101:int) = 
  let Cnode { alloc = i_108_alloc; copy = i_108_copy ;
                                   step = i_108_step ; reset = i_108_reset } = 
  Infer_pf.infer particles_101  metrics  in
  let main_alloc _ =
    ();{ i_108 = i_108_alloc () (* discrete *)  } in
  let main_copy source dest =
    i_108_copy source.i_108 dest.i_108 (* discrete *) in
  let main_reset self  =
    (i_108_reset self.i_108 :unit) in 
  let main_step self (((true_tr_103:((int  * Mat.mat))list) , _) ,
                      (tr_distr_102:(((int  * Mat.mat))list)Distribution.t)) =
    ((let (err_distr_105:(float)Distribution.t) =
          i_108_step self.i_108 (true_tr_103 , tr_distr_102) in
      let (err_104:float) = Distribution.mean_float err_distr_105 in
      err_104):float) in
  Cnode { alloc = main_alloc; copy = main_copy ;
                              reset = main_reset ; step = main_step }
