(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2015                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* clocked ssa language. Cf. minils in LCTES'08 but where *)
(* only equations are annotated with a clock *)

open Sol
      
type eq =
   { eq_lhs: left;
     eq_rhs: exp;
     eq_clk: clock;
     eq_res: reset }

 and clock =
   | Cbase
   | Con of clock * exp * pattern 

 and reset =
   | Cnever
   | Celse of reset * exp

 and left =
   | Cpat of pattern
   | Cset of state
   | Cinit of Ident.t
