(* The Zelus compiler, version 2024-dev
  (2025-01-9-14:43) *)
open Ztypes
type ('e, 'd, 'c, 'b, 'a) machine_50 =
{mutable m_43: 'e;
 mutable m_42: 'd; mutable r_49: 'c; mutable m_47: 'b; mutable m_45: 'a}
type t1 = Zero |Constant of (float) |Linear of (float) 
let m = let machine_50  = 
          
          let machine_50_alloc _ =
            ();
            { m_43 = (T0.Zero:t1);
              m_42 = (Obj.magic ():'e);
              r_49 = (Stdlib.None:('e * t1) Stdlib.option);
              m_47 = ((Obj.magic (), T0.Zero):'e * t1);
              m_45 = ((Obj.magic (), T0.Zero):'e * t1) } in
          let machine_50_reset self  =
            (():unit) in
          let machine_50_step self ((m_42:''a519), (m_43:t1)) =
            (((match self.m_43 with
                 | T0.Zero -> self.r_49 <- Stdlib.None
                 | T0.Constant((m_44:Stdlib.float)) ->
                     self.m_45 <- (self.m_42, T0.Zero);
                     self.r_49 <- Stdlib.Some(self.m_45)
                 | T0.Linear((m_46:Stdlib.float)) ->
                     self.m_47 <- (self.m_42, (T0.Constant(!m_46)));
                     self.r_49 <- Stdlib.Some(self.m_47)
                 ); self.r_49):('e * t1) Stdlib.option) in
          Node { alloc = machine_50_alloc; reset = machine_50_reset;
                                           step = machine_50_step } in
          machine_50

let m = T0.r_32
