(* The Zelus compiler, version 2024-dev
  (2025-06-9-16:9) *)
open Ztypes
type ('d, 'c, 'b, 'a) machine_189 =
{mutable init_183: 'd;
 mutable init_182: 'c; mutable m_179: 'b; mutable m_177: 'a}
type ('d, 'c, 'b, 'a) machine_188 =
{mutable init_181: 'd;
 mutable init_180: 'c; mutable m_175: 'b; mutable m_173: 'a}
let (f) =
      let f_76 =
          (fun (x_77) -> let y_79 = 1 in
                         (+) ((+) ((+) y_79 y_79) x_77) x_77) in
      f_76
let (f1) =
      let f1_82 =
          (fun (x_83) ->
            let y_90 = 2 in
            let x_89 = 1 in
            let z_88 = (+) x_89 1 in
            let y_94 = 2 in
            let x_93 = (+) 1 2 in
            let x_95 = (+) x_93 1 in
            let h_92 = x_95 in
            h_92) in
      f1_82
let (f3) =
      let f3_96 =
          (fun (x_97) ->
            let m_102 =
                (fun (v_103) -> let x_106 = (+) v_103 1 in
                                (+) x_106 2) in
            m_102 2) in
      f3_96
let (my_pid) =
      let my_pid_115 =
          let machine_188 (h_116) (p_119, i_118, d_117) = 
            
            let machine_188_alloc _ =
              ();
              { init_181 = (false:bool);
                init_180 = (false:bool);
                m_175 = ((-1.):float); m_173 = ((-1.):float) } in
            let machine_188_reset self  =
              ((self.init_181 <- true; self.init_180 <- true):unit) in
            let machine_188_step self (u_120) =
              ((self.init_181 <- false;
                (let (p_127, i_126, d_125) = (p_119, i_118, d_117) in
                 let u_135 = ( *. ) d_125 u_120 in
                 let _pre_m_174 = self.m_175 in
                 self.m_175 <- u_135;
                 (let u_131 = ( *. ) i_126 u_120 in
                  let _pre_m_172 = self.m_173 in
                  let o_133 =
                      if self.init_180
                      then 0.
                      else (+.) _pre_m_172 (( *. ) h_116 u_131) in
                  self.init_180 <- false;
                  self.m_173 <- o_133;
                  (+.) ((+.) o_133
                             (if self.init_181
                              then 0.
                              else (/.) ((-.) u_135 _pre_m_174) h_116)) 
                       u_120))):float) in
            Node { alloc = machine_188_alloc; reset = machine_188_reset;
                                              step = machine_188_step } in
            machine_188 in
      my_pid_115
let (controller) =
      let controller_140 =
          let machine_189 (h_141) (p_144, i_143, d_142) = 
            
            let machine_189_alloc _ =
              ();
              { init_183 = (false:bool);
                init_182 = (false:bool);
                m_179 = ((-1.):float); m_177 = ((-1.):float) } in
            let machine_189_reset self  =
              ((self.init_183 <- true; self.init_182 <- true):unit) in
            let machine_189_step self (u_145) =
              ((self.init_183 <- false;
                (let (p_160, i_159, d_158) = (p_144, i_143, d_142) in
                 let u_167 = ( *. ) d_158 u_145 in
                 let _pre_m_178 = self.m_179 in
                 self.m_179 <- u_167;
                 (let u_163 = ( *. ) i_159 u_145 in
                  let _pre_m_176 = self.m_177 in
                  let o_165 =
                      if self.init_182
                      then 0.
                      else (+.) _pre_m_176 (( *. ) h_141 u_163) in
                  self.init_182 <- false;
                  self.m_177 <- o_165;
                  (+.) ((+.) o_165
                             (if self.init_183
                              then 0.
                              else (/.) ((-.) u_167 _pre_m_178) h_141)) 
                       u_145))):float) in
            Node { alloc = machine_189_alloc; reset = machine_189_reset;
                                              step = machine_189_step } in
            machine_189 in
      controller_140
