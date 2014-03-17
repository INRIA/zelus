
(* Functions for comparing times *)
val time_eq   : float -> float -> bool
val time_leq  : float -> float -> bool
val time_geq  : float -> float -> bool

(* Add another argument to the list returned by args *)
val add_custom_arg : (Arg.key * Arg.spec * Arg.doc) -> unit

module type ZELUS_SOLVER =
sig
  (** Interface for compiled functions *)

  (* Abstract types for the vectors passed to the model functions. Elements
     are accessed or changed by the functions given below. *)

  type cvector  (* array of continuous states *)
  type zvector  (* array of zero-crossing flags *)
  type zxvector (* array of zero-crossing values *)

  val get_cs : cvector  -> int -> float
  val set_cs : cvector  -> int -> float -> unit
  val get_zc : zvector  -> int -> bool
  val set_zx : zxvector -> int -> float -> unit

  (* (x, dx, upz, z, discrete, time) -> (result, goagain, next_time) *)
  type 'a single_f =
    cvector * cvector * zxvector * zvector * bool * float -> 'a * bool * float

  (**
    The type of a function passed to a numerical solver for state
    approximation. A function [f (x, dx)] is given an input vector of
    continuous states [x], which it must only read, and an "empty" vector [dx]
    into which it must write all instantaneous derivatives. Nothing should be
    assumed about the initial contents of [dx].
   *)
  type model_der = cvector * cvector -> unit

  (**
    The type of a function passed to a numerical solver for detecting
    zero-crossings. A function [g (x, ze)] is given an input vector of
    continuous states [x], which it must only read, and an "empty" vector [ze]
    into which it must write values for all zero-crossing expressions. Nothing
    should be assumed about the initial contents of [ze].
  *)
  type model_zero = cvector * zxvector -> unit

  type model_disc_next =
    | Continue of bool * float
    | Goagain of bool
    | EndSimulation

  (**
    The type of a function used to compute discrete reactions. A function
    [(r, n) = d (x, z, t)] is passed a vector of continuous states [x], which
    it may change, an input vector of zero-crossing flags [z], and the current
    simulation time [t]. It returns a result [r], which is currently ignored,
    and a instruction about what to do next:

      [Continue (reset, horizon)]   reset the solver if necessary and then
                                    pass control to the numeric solver with
                                    the given horizon.

      [Goagain reset]               trigger another discrete reaction,
                                    indicating whether the solver should be
                                    reset before the beginning of any subsequent
                                    continous phase.

      [Endsimulation]               stop the simulation

    The solver must be reset if any element in [x] has been modified. It
    should normally be reset if the governing dynamic equations have been
    chnaged.
  *)
  type 'a model_disc = cvector * zvector * float -> 'a * model_disc_next

  type 'a compiled_model = {
    f_der : model_der;
    f_zero : model_zero;
    f_disc : 'a model_disc;

    (* called once before a simulation begins *)
    num_cstates : unit -> int;

    (* called once before a simulation begins and after all discrete calls *)
    num_zeros : unit -> int;
  }

  (* [(der_f, zero_f, disc_f) =  split_single n_states n_roots fgd] provides
     legacy support for the old "single function" interface. *)
  val split_single : int -> int -> 'a single_f -> 'a compiled_model

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

  (* Simulations are executed as follows:
   *    let ss = ref (main model) in
   *    while not (is_done ss) do
   *      r, ss := step !ss
   *    done
   *)
  type 'a sim_state

  val main  : 'a compiled_model -> 'a sim_state
  val main' : (int * int) -> 'a single_f -> 'a sim_state

  (* The result returned by step is [None] after a continuous step and
   * [Some x] after a discrete step, where [x] is the value returned by
   * the main function.
   *)

  (* Given the current [sim_state], execute one step of the simulation and
   * return the tuple (result, wallclk_delta, sim_state'). The [result] is
   * [None] after a continuous step and [Some x] after a discrete step, where
   * [x] is the value returned by the main function.
   *
   * [wallclk_delta] gives a rough indication of the amount of clock time that
   * should elapse during the step. It is equal to 0 after a discrete step and
   * greater than 0 after a continuous step--the exact value is the amount of
   * simulation time that elapsed during the continuous step divided by a
   * speedup factor. A simulation loop could try to synchronize simulation and
   * wall clock time by executing [step] again after [wallclk_delta] seconds
   * have elapsed, i.e., straight away after a discrete step and delayed after a
   * continuous phase. Simulation loops should try to account for the time lost
   * in executing [step].
   *
   * Note that any external events that occur during the wall-clock delay will
   * be detected at the next discrete step. This is normal for sample-driven
   * execution, but inadequate for event-driven execution (which would have to,
   * at a minimum, interrupt the delay, interpolate or calculate continuous
   * states up to the simulation time corresponding to the wall clock time
   * (i.e., to relate the two times in the other direction) and then to execute
   * a dicrete step and communicate the triggering event as a kind of "external
   * zero-crossing". Accounting for computation time in this case is likely to
   * be problematic. Such event-driven execution is not supported!
   *)
  val step      : 'a sim_state -> 'a option * float * 'a sim_state
  val is_done   : 'a sim_state -> bool

  (** Adding command-line arguments *)

  (* Given the number of continuous states in the system being simulated,
   * return a list that can be passed to Arg.parse to allow simulation
   * parameters to be set at the command line. *)
  val args : int -> (Arg.key * Arg.spec * Arg.doc) list
end

module Instantiate :
  functor (Solver : Solvers.SOLVER) ->
          (ZELUS_SOLVER with type cvector  = Solver.cvec
                        and type zvector  = Solver.zvec
                        and type zxvector = Solver.zxvec)

(* v' = add_epsilons n v
 * Utility function that adds n library-defined 'epsilons' to v. If n is
 * negative than the epilsons are subtracted. *)
val add_epsilons    : int -> float -> float

(* Utility function for constructing command-line arguments that set the initial
 * value of particular state variables.
 *   ("-velocity", set_float_delta velocity_i, "Set the initial velocity.")
 * The value is parsed using %e and may be followed by a string of '+' and '-'
 * characters, for each '+' an 'epsilon' is added to the value, and for each '-'
 * it is subtracted.
 *)
val set_float_delta : float ref -> Arg.spec

val set_default_solver : string -> unit

val register' : string
                -> Arg.key * Arg.spec * Arg.doc
                -> (module Solvers.SOLVER)
                -> unit

val register : string
               -> Arg.doc
               -> (module Solvers.SOLVER)
               -> unit

val instantiate : unit -> (module ZELUS_SOLVER)

val check_for_solver : string array -> unit

