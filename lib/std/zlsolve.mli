
(* Abstract types for the vectors passed to the model functions. Elements
   are accessed or changed by the functions given below. *)

module type ZELUS_SOLVER =
sig
  (** Interface for compiled functions *)

  (** Configuring and calling the D-C solver *)

  (* Log simulation steps and continuous state values. *)
  val enable_logging       : unit -> unit

  (* The solver's minimum and maxmium step sizes. *)
  val min_step_size : float option ref
  val max_step_size : float option ref

  (* The maximum simulation time. *)
  val max_sim_time  : float option ref

  (* A factor relating simulation and wall clock times. *)
  val speedup       : float ref

  val step  :    's Zls.f_alloc
              -> 's Zls.f_csize
              -> 's Zls.f_zsize
              -> 's Zls.f_horizon
              -> 's Zls.f_maxsize
              -> 's Zls.f_ders
              -> ('s, 'o) Zls.f_step
              -> 's Zls.f_zero
              -> 's Zls.f_reset
              -> (unit -> 'o option * bool * float) (* result, is_done, delta *)
end

module Make :  functor (SSolver : Zls.STATE_SOLVER)
               -> functor (ZSolver : Zls.ZEROC_SOLVER)
               -> ZELUS_SOLVER

