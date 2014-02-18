(***********************************************************************)
(*                                                                     *)
(*              Ocaml interface to Sundials CVODE solver               *)
(*                                                                     *)
(*           Timothy Bourke (INRIA) and Marc Pouzet (LIENS)            *)
(*                                                                     *)
(*  Copyright 2013 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file LICENSE.        *)
(*                                                                     *)
(***********************************************************************)

(***********************************************************************)
(* Much of the comment text is taken directly from:                    *)
(*                                                                     *)
(*               User Documentation for CVODE v2.6.0                   *)
(*                Alan C. Hindmarsh and Radu Serban                    *)
(*              Center for Applied Scientific Computing                *)
(*              Lawrence Livermore National Laboratory                 *)
(*                                                                     *)
(***********************************************************************)

include module type of Cvode

(*STARTINTRO*)
(** Serial nvector interface to the CVODE solver.
 
  Serial vectors are passed between Sundials and Ocaml programs as
  Bigarrays.
  These vectors are manipulated within the solver using the original low-level
  vector operations (cloning, linear sums, adding constants, and etcetera).
  While direct interfaces to these operations are not provided, there are
  equivalent implementations written in Ocaml for arrays of floats
  ({! Nvector_array}) and bigarrays ({! Nvector_array.Bigarray}) of floats.

  @version VERSION()
  @author Timothy Bourke (INRIA)
  @author Marc Pouzet (LIENS)
 *)

(**
    This type represents a session with the CVODE solver using serial nvectors
    accessed as {{:OCAML_DOC_ROOT(Bigarray.Array1)} Bigarray.Array1}s.

    A skeleton of the main program:
    + {b Set vector of initial values}
    {[let y = Cvode.Carray.of_array [| 0.0; 0.0; 0.0 |] ]}
    The length of this vector determines the problem size.    
    + {b Create and initialize a solver session}
    {[let s = Cvode.init Cvode.Adams Cvode.Functional f (2, g) y]}
    This will initialize a specific linear solver and the root-finding
    mechanism, if necessary.
    + {b Specify integration tolerances (optional)}, e.g.
    {[ss_tolerances s reltol abstol]}
    + {b Set optional inputs}, e.g.
    {[set_stop_time s 10.0; ...]}
    Call any of the [set_*] functions to change solver parameters from their
    defaults.
    + {b Advance solution in time}, e.g.
    {[let (t', result) = Cvode.normal s !t y in
...
t := t' + 0.1]}
    Repeatedly call either [normal] or [one_step] to advance the simulation.
    + {b Get optional outputs}
    {[let stats = get_integrator_stats s in ...]}
    Call any of the [get_*] functions to examine solver statistics.

    @cvode <node5#ss:skeleton_sim> Skeleton of main program
 *)
(*ENDINTRO*)
type session

(** The type of vectors passed to the solver. *)
type nvec = Sundials.Carray.t

(** The type of vectors containing dependent variable values, passed from the
   solver to callback functions. *)
type val_array = Sundials.Carray.t

(** The type of vectors containing derivative values, passed from the
   solver to callback functions. *)
type der_array = Sundials.Carray.t

(** The type of vectors containing detected roots (zero-crossings). *)
type root_array = Sundials.Roots.t

(** The type of vectors containing the values of root functions
   (zero-crossings). *)
type root_val_array = Sundials.Roots.val_array

(** {2 Initialization} *)

(**
    [init lmm iter f (nroots, g) y0] initializes the CVODE solver and returns a
    {!session}.
    - [lmm]     specifies the linear multistep method, see {!Cvode.lmm}.
    - [iter]    specifies either functional iteration or Newton iteration
                with a specific linear solver, see {!Cvode.iter}.
    - [f]       is the ODE right-hand side function.
    - [nroots]  specifies the number of root functions (zero-crossings).
    - [g]       calculates the values of the root functions.
    - [y0]      is a vector of initial values, the size of this vector
                determines the number of equations in  the session, see
                {!Sundials.Carray.t}.

    The start time defaults to 0. It can be set manually by instead using
    {!init'}.

    This function calls CVodeCreate, CVodeInit, CVodeRootInit, an appropriate
    linear solver function, and CVodeSStolerances (with default values for
    relative tolerance of 1.0e-4 and absolute tolerance as 1.0e-8; these can be
    changed with {!ss_tolerances}, {!sv_tolerances}, or {!wf_tolerances}).
    It does everything necessary to initialize a CVODE session; the {!normal} or
    {!one_step} functions can be called directly afterward.

    The right-hand side function [f] is called by the solver to calculate the
    instantaneous derivative values, it is passed three arguments: [t], [y], and
    [dy].
    - [t] is the current value of the independent variable,
          i.e., the simulation time.
    - [y] is a vector of dependent-variable values, i.e. y(t).
    - [dy] is a vector for storing the value of f(t, y).

    {b NB:} [y] and [dy] must no longer be accessed after [f] has returned a
            result, i.e. if their values are needed outside of the function
            call, then they must be copied to separate physical structures.

    The roots function [g] is called by the solver to calculate the values of
    root functions (zero-crossing expressions) which are used to detect
    significant events, it is passed three arguments: [t], [y], and [gout].
    - [t] and [y] are as for [f].
    - [gout] is a vector for storing the values of g(t, y).
    The {!Cvode.no_roots} value can be passed for the [(nroots, g)] argument if
    root functions are not required.

    {b NB:} [y] and [gout] must no longer be accessed after [g] has returned
            a result, i.e. if their values are needed outside of the function
            call, then they must be copied to separate physical structures.

    @cvode <node5#sss:cvodemalloc>   CVodeCreate/CVodeInit
    @cvode <node5#ss:rhsFn>          ODE right-hand side function
    @cvode <node5#ss:cvrootinit>     CVodeRootInit
    @cvode <node5#ss:rootFn>         Rootfinding function
    @cvode <node5#sss:lin_solv_init> Linear solvers
    @cvode <node5#sss:cvtolerances> CVodeSStolerances
 *)
val init :
    lmm
    -> iter
    -> (float -> val_array -> der_array -> unit)
    -> (int * (float -> val_array -> root_val_array -> unit))
    -> nvec
    -> session

(**
  [init lmm iter f roots y0 t0] is the same as init' except that a start time,
  [t0], can be given explicitly.
 *)
val init' :
    lmm
    -> iter
    -> (float -> val_array -> der_array -> unit)
    -> (int * (float -> val_array -> root_val_array -> unit))
    -> nvec
    -> float (* start time *)
    -> session

(** Return the number of root functions. *)
val nroots : session -> int

(** Return the number of equations. *)
val neqs : session -> int

(** {2 Tolerance specification} *)

(**
    [ss_tolerances s reltol abstol] sets the relative and absolute
    tolerances using scalar values.

    @cvode <node5#sss:cvtolerances> CVodeSStolerances
 *)
val ss_tolerances : session -> float -> float -> unit

(**
    [sv_tolerances s reltol abstol] sets the relative tolerance using a scalar
    value, and the absolute tolerance as a vector.

    @cvode <node5#sss:cvtolerances> CVodeSVtolerances
 *)
val sv_tolerances : session -> float -> nvec -> unit

(**
    [wf_tolerances s efun] specifies a function [efun] that sets the multiplicative
    error weights Wi for use in the weighted RMS norm.

    [efun y ewt] is passed the dependent variable vector [y] and is expected to
    set the values inside the error-weight vector [ewt].

    @cvode <node5#sss:cvtolerances> CVodeWFtolerances
    @cvode <node5#ss:ewtsetFn> Error weight function
 *)
val wf_tolerances : session -> (val_array -> val_array -> unit) -> unit

(** {2 Solver functions } *)

(**
   [(tret, r) = normal s tout yout] integrates the ODE over an interval in t.

   The arguments are:
   - [s] a session with the solver.
   - [tout] the next time at which a computed solution is desired.
   - [yout] a vector to store the computed solution. The same vector as was
   passed to {!init} can be used again for this argument.

   Two values are returned:
    - [tret] the time reached by the solver, which will be equal to [tout] if
      no errors occur.
    - [r] indicates whether roots were found, or whether an optional stop time, set by
    {!set_stop_time}, was reached; see {!Cvode.solver_result}.

   This routine will throw one of the solver {!Cvode.exceptions} if an error
   occurs.

   @cvode <node5#sss:cvode> CVode (CV_NORMAL)
 *)
val normal : session -> float -> nvec -> float * solver_result

(**
   This function is identical to {!normal}, except that it returns after one
   internal solver step.

   @cvode <node5#sss:cvode> CVode (CV_ONE_STEP)
 *)
val one_step : session -> float -> nvec -> float * solver_result

(** {2 Main optional functions} *)

(** {3 Input} *)

(**
  [set_error_file s fname trunc] opens the file named [fname] and to which all
  messages from the default error handler are then directed.
  If the file already exists it is either trunctated ([trunc] = [true]) or
  appended to ([trunc] = [false]).

  The error file is closed if set_error_file is called again, or otherwise when
  the session is garbage collected.
   
  @cvode <node5#sss:optin_main> CVodeSetErrFile
 *)
val set_error_file : session -> string -> bool -> unit

(**
  [set_err_handler_fn s efun] specifies a custom function [efun] for handling
  error messages.

  @cvode <node5#sss:optin_main> CVodeSetErrHandlerFn
  @cvode <node5#ss:ehFn> Error message handler function
 *)
val set_err_handler_fn : session -> (error_details -> unit) -> unit

(**
  This function restores the default error handling function. It is equivalent
  to calling CVodeSetErrHandlerFn with an argument of [NULL].

  @cvode <node5#sss:optin_main> CVodeSetErrHandlerFn
 *)
val clear_err_handler_fn : session -> unit

(**
  Specifies the maximum order of the linear multistep method.

  @cvode <node5#sss:optin_main> CVodeSetMaxOrd
 *)
val set_max_ord : session -> int -> unit

(**
  Specifies the maximum number of steps to be taken by the solver in its attempt
  to reach the next output time.

  @cvode <node5#sss:optin_main> CVodeSetMaxNumSteps
 *)
val set_max_num_steps : session -> int -> unit

(**
  Specifies the maximum number of messages issued by the solver warning that t +
  h = t on the next internal step.

  @cvode <node5#sss:optin_main> CVodeSetMaxHnilWarns
 *)
val set_max_hnil_warns : session -> int -> unit

(**
  Indicates whether the BDF stability limit detection algorithm should be used.

  @cvode <node5#sss:optin_main> CVodeSetStabLimDet
  @cvode <node3#s:bdf_stab> BDF Stability Limit Detection
 *)
val set_stab_lim_det : session -> bool -> unit

(**
  Specifies the initial step size.

  @cvode <node5#sss:optin_main> CVodeSetInitStep
 *)
val set_init_step : session -> float -> unit

(**
  Specifies a lower bound on the magnitude of the step size.

  @cvode <node5#sss:optin_main> CVodeSetMinStep
 *)
val set_min_step : session -> float -> unit

(**
  Specifies an upper bound on the magnitude of the step size.

  @cvode <node5#sss:optin_main> CVodeSetMaxStep
 *)
val set_max_step : session -> float -> unit

(**
  Specifies the value of the independent variable t past which the solution is
  not to proceed.
  The default, if this routine is not called, is that no stop time is imposed.

  @cvode <node5#sss:optin_main> CVodeSetStopTime
 *)
val set_stop_time : session -> float -> unit

(**
  Specifies the maximum number of error test failures permitted in attempting
  one step.

  @cvode <node5#sss:optin_main> CVodeSetMaxErrTestFails
 *)
val set_max_err_test_fails : session -> int -> unit

(**
  Specifies the maximum number of nonlinear solver iterations permitted per
  step.

  @cvode <node5#sss:optin_main> CVodeSetMaxNonlinIters
 *)
val set_max_nonlin_iters : session -> int -> unit

(**
  Specifies the maximum number of nonlinear solver convergence failures
  permitted during one step.

  @cvode <node5#sss:optin_main> CVodeSetMaxConvFails
 *)
val set_max_conv_fails : session -> int -> unit

(**
  Specifies the safety factor used in the nonlinear convergence test.

  @cvode <node5#sss:optin_main> CVodeSetNonlinConvCoef
  @cvode <node3#ss:ivp_sol> IVP Solution
 *)
val set_nonlin_conv_coef : session -> float -> unit

(**
  [set_iter_type s iter] resets the nonlinear solver iteration type to [iter]
  ({!Cvode.iter}).

  @cvode <node5#sss:optin_main> CVodeSetIterType
 *)
val set_iter_type : session -> iter -> unit

(** {3 Output } *)

(**
  Returns the real and integer workspace sizes.

  @cvode <node5#sss:optout_main> CVodeGetWorkSpace
  @return ([real_size], [integer_size])
 *)
val get_work_space          : session -> int * int

(**
  Returns the cumulative number of internal steps taken by the solver.

  @cvode <node5#sss:optout_main> CVodeGetNumSteps
 *)
val get_num_steps           : session -> int

(**
  Returns the number of calls to the user's right-hand side function.

  @cvode <node5#sss:optout_main> CVodeGetNumRhsEvals
 *)
val get_num_rhs_evals       : session -> int

(**
  Returns the number of calls made to the linear solver's setup function.

  @cvode <node5#sss:optout_main> CVodeGetNumLinSolvSetups
 *)
val get_num_lin_solv_setups : session -> int

(**
  Returns the number of local error test failures that have occurred.

  @cvode <node5#sss:optout_main> CVodeGetNumErrTestFails
 *)
val get_num_err_test_fails  : session -> int

(**
  Returns the integration method order used during the last internal step.

  @cvode <node5#sss:optout_main> CVodeGetLastOrder
 *)
val get_last_order          : session -> int

(**
  Returns the integration method order to be used on the next internal step.

  @cvode <node5#sss:optout_main> CVodeGetCurrentOrder
 *)
val get_current_order       : session -> int

(**
  Returns the integration step size taken on the last internal step.

  @cvode <node5#sss:optout_main> CVodeGetLastStep
 *)
val get_last_step           : session -> float

(**
  Returns the integration step size to be attempted on the next internal step.

  @cvode <node5#sss:optout_main> CVodeGetCurrentStep
 *)
val get_current_step        : session -> float

(**
  Returns the the value of the integration step size used on the first step.

  @cvode <node5#sss:optout_main> CVodeGetActualInitStep
 *)
val get_actual_init_step    : session -> float

(**
  Returns the the current internal time reached by the solver.

  @cvode <node5#sss:optout_main> CVodeGetCurrentTime
 *)
val get_current_time        : session -> float

(**
  Returns the number of order reductions dictated by the BDF stability limit
  detection algorithm.

  @cvode <node5#sss:optout_main> CVodeGetNumStabLimOrderReds
  @cvode <node3#s:bdf_stab> BDF stability limit detection
 *)
val get_num_stab_lim_order_reds : session -> int

(**
  Returns a suggested factor by which the user's tolerances should be scaled
  when too much accuracy has been requested for some internal step.

  @cvode <node5#sss:optout_main> CVodeGetTolScaleFactor
 *)
val get_tol_scale_factor : session -> float

(**
  Returns the solution error weights at the current time.

  @cvode <node5#sss:optout_main> CVodeGetErrWeights
  @cvode <node3#ss:ivp_sol> IVP solution (W_i)
 *)
val get_err_weights : session -> nvec -> unit

(**
  Returns the vector of estimated local errors.

  @cvode <node5#sss:optout_main> CVodeGetEstLocalErrors
 *)
val get_est_local_errors : session -> nvec -> unit

(**
  Returns the integrator statistics as a group.

  @cvode <node5#sss:optout_main> CVodeGetIntegratorStats
 *)
val get_integrator_stats    : session -> Cvode.integrator_stats

(**
  Convenience function that calls get_integrator_stats and prints the results to
  stdout.

  @cvode <node5#sss:optout_main> CVodeGetIntegratorStats
 *)
val print_integrator_stats  : session -> unit


(**
  Returns the number of nonlinear (functional or Newton) iterations performed.

  @cvode <node5#sss:optout_main> CVodeGetNumNonlinSolvIters
 *)
val get_num_nonlin_solv_iters : session -> int

(**
  Returns the number of nonlinear convergence failures that have occurred.

  @cvode <node5#sss:optout_main> CVodeGetNumNonlinSolvConvFails
 *)
val get_num_nonlin_solv_conv_fails : session -> int

(** {2 Root finding optional functions} *)

(** {3 Input} *)

(**
  [set_root_direction s dir] specifies the direction of zero-crossings to be
  located and returned. [dir] may contain one entry of type
  {!Cvode.root_direction} for each root function.

  @cvode <node5#sss:optin_root> CVodeSetRootDirection
 *)
val set_root_direction : session -> root_direction array -> unit

(**
  Like {!set_root_direction} but specifies a single direction of type
  {!Cvode.root_direction} for all root
  functions.

  @cvode <node5#sss:optin_root> CVodeSetRootDirection
 *)
val set_all_root_directions : session -> root_direction -> unit

(**
  Disables issuing a warning if some root function appears to be identically
  zero at the beginning of the integration.

  @cvode <node5#sss:optin_root> CVodeSetNoInactiveRootWarn
 *)
val set_no_inactive_root_warn : session -> unit

(** {3 Output} *)

(**
  Fills an array showing which functions were found to have a root.

  @cvode <node5#sss:optout_root> CVodeGetRootInfo
 *)
val get_root_info : session -> root_array -> unit

(**
  Returns the cumulative number of calls made to the user-supplied root function g.

  @cvode <node5#sss:optout_root> CVodeGetNumGEvals
 *)
val get_num_g_evals : session -> int

(** {2 Interpolated output function } *)

(**
  [get_dky s t k dky] computes the [k]th derivative of the function y at time
  [t], i.e. d(k)y/dt(k)(t). The function requires that tn - hu <= [t] <=
  tn, where tn denotes the current internal time reached, and hu is the last
  internal step size successfully used by the solver.
  The user may request [k] = 0, 1,..., qu, where qu is the current order.

  This function may only be called after a successful return from either
  {!normal} or {!one_step}.

  Values for the limits may be obtained:
    - tn = {!get_current_time}
    - qu = {!get_last_order}
    - hu = {!get_last_step}

  @cvode <node5#sss:optin_root> CVodeGetDky
 *)
val get_dky : session -> float -> int -> nvec -> unit

(** {2 Reinitialization} *)

(**
  [reinit s t0 y0] reinitializes the solver session [s] with a new time [t0] and
  new values for the variables [y0].

  @cvode <node5#sss:cvreinit> CVodeReInit
 *)
val reinit : session -> float -> nvec -> unit


(** {2 Linear Solvers} *)

type single_tmp = val_array
type triple_tmp = val_array * val_array * val_array

(**
  Arguments common to all Jacobian callback functions.    
 
  @cvode <node5#ss:djacFn> Dense Jacobian function
  @cvode <node5#ss:bjacFn> Banded Jacobian function
  @cvode <node5#ss:jtimesFn> Product Jacobian function
  @cvode <node5#ss:psolveFn> Linear preconditioning function
  @cvode <node5#ss:precondFn> Jacobian preconditioning function
 *)
type 't jacobian_arg =
  {
    jac_t   : float;        (** The independent variable. *)
    jac_y   : val_array;    (** The dependent variable vector. *)
    jac_fy  : val_array;    (** The derivative vector (i.e. f(t, y)). *)
    jac_tmp : 't            (** Workspace data,
                                either {!single_tmp} or {!triple_tmp}. *)
  }

(** {3 Direct Linear Solvers (DLS)} *)

(** Control callbacks and get optional outputs for the Direct Linear Solvers
    that operate on dense and banded matrices.
    
    @cvode <node5#sss:optin_dls> Direct linear solvers optional input functions
    @cvode <node5#sss:optout_dls> Direct linear solvers optional output functions
    @cvode <node5#ss:djacFn> Dense Jacobian function
  *)
module Dls :
  sig
    (** {4 Callback functions} *)
    (**
     Specify a callback function that computes an approximation to the Jacobian
     matrix J(t, y) for the Dense and Lapackdense {!Cvode.linear_solver}s.

     The callback function takes the {!jacobian_arg} as an input and must store
     the computed Jacobian as a {!Cvode.Densematrix.t}.

     {b NB:} the elements of the Jacobian argument and the output matrix must no
     longer be accessed after callback function has returned a result, i.e. if
     their values are needed outside of the function call, then they must be
     copied to separate physical structures.
     
     @cvode <node5#sss:optin_dls> CVDlsSetDenseJacFn
     @cvode <node5#ss:djacFn> Dense Jacobian function
     *)
    val set_dense_jac_fn :
         session
      -> (triple_tmp jacobian_arg -> Densematrix.t -> unit)
      -> unit

    (**
      This function disables the user-supplied dense Jacobian function, and
      switches back to the default internal difference quotient approximation
      that comes with the Dense and Lapackdense {!Cvode.linear_solver}s. It is
      equivalent to calling CVodeSetDenseJacFn with an argument of [NULL].

      @cvode <node5#ss:djacFn> Dense Jacobian function
    *)
    val clear_dense_jac_fn : session -> unit

    (**
     Specify a callback function that computes an approximation to the Jacobian
     matrix J(t, y) for the Band and Lapackband {!Cvode.linear_solver}s.

     The callback function takes three input arguments:
     - [jac] the standard {!jacobian_arg} with three work vectors.
     - [mupper] the upper half-bandwidth of the Jacobian.
     - [mlower] the lower half-bandwidth of the Jacobian.
     and it must store the computed Jacobian as a {!Cvode.Bandmatrix.t}.

    {b NB:} [jac] and the computed Jacobian must no longer be accessed after the
            calback function has returned a result, i.e. if their values are
            needed outside of the function call, then they must be copied to
            separate physical structures.

     @cvode <node5#sss:optin_dls> CVDlsSetBandJacFn
     @cvode <node5#ss:bjacFn> Banded Jacobian function
     *)
    val set_band_jac_fn :
         session
      -> (triple_tmp jacobian_arg -> int -> int -> Bandmatrix.t -> unit)
      -> unit

    (**
      This function disables the user-supplied band Jacobian function, and
      switches back to the default internal difference quotient approximation
      that comes with the Band and Lapackband {!Cvode.linear_solver}s. It is
      equivalent to calling CVodeSetBandJacFn with an argument of [NULL].

      @cvode <node5#ss:bjacFn> Banded Jacobian function
    *)
    val clear_band_jac_fn : session -> unit

    (** {4 Optional input functions} *)

    (**
      Returns the sizes of the real and integer workspaces used by the Dense and
      Band direct linear solvers .

      @cvode <node5#sss:optout_dls> CVDlsGetWorkSpace
      @return ([real_size], [integer_size])
     *)
    val get_work_space : session -> int * int


    (**
      Returns the number of calls made to the Dense and Band direct linear
      solvers Jacobian approximation function.

      @cvode <node5#sss:optout_dls> CVDlsGetNumJacEvals
    *)
    val get_num_jac_evals : session -> int

    (**
      Returns the number of calls made to the user-supplied right-hand side
      function due to the finite difference (Dense or Band) Jacobian
      approximation.

      @cvode <node5#sss:optout_dls> CVDlsGetNumRhsEvals
    *)
    val get_num_rhs_evals : session -> int
  end

(** {3 Diagonal approximation} *)

(** Get optional inputs for the linear solver that gives diagonal approximations
    of the Jacobian matrix.
    @cvode <node5#sss:optout_diag> Diagonal linear solver optional output functions
  *)
module Diag :
  sig
    (** {4 Optional input functions} *)

    (**
      Returns the sizes of the real and integer workspaces used by the Diagonal
      linear solver.

      @cvode <node5#sss:optout_diag> CVDiagGetWorkSpace
      @return ([real_size], [integer_size])
     *)
    val get_work_space : session -> int * int

    (**
      Returns the number of calls made to the user-supplied right-hand side
      function due to finite difference Jacobian approximation in the Diagonal
      linear solver.

      @cvode <node5#sss:optout_diag> CVDiagGetNumRhsEvals
    *)
    val get_num_rhs_evals : session -> int
  end

(** {3 Scaled Preconditioned Iterative Linear Solvers (SPILS)} *)

(** Set callback functions, set optional outputs, and get optional inputs for
    the Scaled Preconditioned Iterative Linear Solvers: SPGMR, SPBCG, SPTFQMR.
    @cvode <node5#sss:optin_spils> Iterative linear solvers optional input functions.
    @cvode <node5#sss:optout_spils> Iterative linear solvers optional output functions.
    @cvode <node5#ss:psolveFn> Linear preconditioning function
    @cvode <node5#ss:precondFn> Jacobian preconditioning function
 *)
module Spils :
  sig
    (** {4 Callback functions} *)

    (**
      Arguments passed to the preconditioner solve callback function.

      @cvode <node5#ss:psolveFn> CVSpilsPrecSolveFn
     *)
    type solve_arg =
      {
        rhs   : val_array;  (** The right-hand side vector, {i r}, of the
                                linear system. *)
        gamma : float;      (** The scalar {i g} appearing in the Newton
                                matrix given by M = I - {i g}J. *)
        delta : float;      (** Input tolerance to be used if an
                                iterative method is employed in the
                                solution. *)
        left  : bool;       (** [true] (1) if the left preconditioner
                                is to be used and [false] (2) if the
                                right preconditioner is to be used. *)
      }

    (**
      Setup preconditioning for any of the SPILS linear solvers. Two functions
      are required: [psetup] and [psolve].

      [psetup jac jok gamma] preprocesses and/or evaluates any Jacobian-related
      data needed by the preconditioner. It takes three inputs:
        - [jac] supplies the basic problem data as a {!jacobian_arg}.
        - [jok] indicates whether any saved Jacobian-related data can be reused.
        If [false] any such data must be recomputed from scratch, otherwise, if
        [true], any such data saved from a previous call to the function can
        be reused, with the current value of [gamma]. A call with [jok] =
        [true] can only happen after an earlier call with [jok] = [false].
        - [gamma] is the scalar {i g} appearing in the Newton matrix given
        by M = I - {i g}J.

      {b NB:} The elements of [jac] must no longer be accessed after [psetup]
              has returned a result, i.e. if their values are needed outside
              of the function call, then they must be copied to a separate
              physical structure.

      It must return [true] if the Jacobian-related data was updated, or
      [false] otherwise, i.e. if the saved data was reused.

      [psolve jac arg z] is called to solve the linear system
      {i P}[z] = [jac.rhs], where {i P} may be either a left or right
      preconditioner matrix. {i P} should approximate, however crudely, the
      Newton matrix M = I - [jac.gamma] J, where J = delr(f) / delr(y).
      - [jac] supplies the basic problem data as a {!jacobian_arg}.
      - [arg] specifies the linear system as a {!solve_arg}.
      - [z] is the vector in which the result must be stored.

      {b NB:} The elements of [jac], [arg], and [z] must no longer be accessed
              after [psolve] has returned a result, i.e. if their values are
              needed outside of the function call, then they must be copied
              to separate physical structures.

      @cvode <node5#sss:optin_spils> CVSpilsSetPreconditioner
      @cvode <node5#ss:psolveFn> Linear preconditioning function
      @cvode <node5#ss:precondFn> Jacobian preconditioning function
    *)
    val set_preconditioner :
      session
      -> (triple_tmp jacobian_arg -> bool -> float -> bool)
      -> (single_tmp jacobian_arg -> solve_arg -> nvec -> unit)
      -> unit

    (**
      Specifies a Jacobian-vector function.

      The function given, [jactimes jac v Jv], computes the matrix-vector
      product {i J}[v].
      - [v] is the vector by which the Jacobian must be multiplied.
      - [Jv] is the vector in which the result must be stored.

      {b NB:} The elements of [jac], [v], and [Jv] must no longer be accessed
              after [psolve] has returned a result, i.e. if their values are
              needed outside of the function call, then they must be copied
              to separate physical structures.

      @cvode <node5#sss:optin_spils> CVSpilsSetJacTimesVecFn
      @cvode <node5#ss:jtimesFn> Product Jacobian function
    *)
    val set_jac_times_vec_fn :
      session
      -> (single_tmp jacobian_arg
          -> val_array (* v *)
          -> val_array (* Jv *)
          -> unit)
      -> unit

    (**
      This function disables the user-supplied Jacobian-vector function, and
      switches back to the default internal difference quotient approximation.
      It is equivalent to calling CVSpilsSetJacTimesVecFn with an argument of
      [NULL].

      @cvode <node5#sss:optin_spils> CVSpilsSetJacTimesVecFn
      @cvode <node5#ss:jtimesFn> Product Jacobian function
    *)
    val clear_jac_times_vec_fn : session -> unit

    (** {4 Optional output functions} *)

    (**
      This function resets the type of preconditioning to be used using a value
      of type {!Cvode.preconditioning_type}.

      @cvode <node5#sss:optin_spils> CVSpilsSetPrecType
    *)
    val set_prec_type : session -> preconditioning_type -> unit

    (** Constants representing the types of Gram-Schmidt orthogonalization
        possible for the Spgmr {Cvode.linear_solver}. *)
    type gramschmidt_type =
      | ModifiedGS
            (** Modified Gram-Schmidt orthogonalization (MODIFIED_GS) *)
      | ClassicalGS
            (** Classical Gram Schmidt orthogonalization (CLASSICAL_GS) *)

    (**
      Sets the Gram-Schmidt orthogonalization to be used with the
      Spgmr {!Cvode.linear_solver}.

      @cvode <node5#sss:optin_spils> CVSpilsSetGSType
    *)
    val set_gs_type : session -> gramschmidt_type -> unit

    (**
      [set_eps_lin eplifac] sets the factor by which the Krylov linear solver's
      convergence test constant is reduced from the Newton iteration test
      constant. [eplifac]  must be >= 0. Passing a value of 0 specifies the
      default (which is 0.05).

      @cvode <node5#sss:optin_spils> CVSpilsSetEpsLin
    *)
    val set_eps_lin : session -> float -> unit

    (**
      [set_maxl maxl] resets the maximum Krylov subspace dimension for the
      Bi-CGStab or TFQMR methods. [maxl] is the maximum dimension of the Krylov
      subspace, a value of [maxl] <= 0 specifies the default (which is 5.0).

      @cvode <node5#sss:optin_spils> CVSpilsSetMaxl
    *)
    val set_maxl : session -> int -> unit

    (** {4 Optional input functions} *)

    (**
      Returns the sizes of the real and integer workspaces used by the SPGMR
      linear solver.

      @cvode <node5#sss:optout_spils> CVSpilsGetWorkSpace
      @return ([real_size], [integer_size])
    *)
    val get_work_space       : session -> int * int

    (**
      Returns the cumulative number of linear iterations.

      @cvode <node5#sss:optout_spils> CVSpilsGetNumLinIters
    *)
    val get_num_lin_iters    : session -> int

    (**
      Returns the cumulative number of linear convergence failures.

      @cvode <node5#sss:optout_spils> CVSpilsGetNumConvFails
    *)
    val get_num_conv_fails   : session -> int

    (**
      Returns the number of preconditioner evaluations, i.e., the number of
      calls made to psetup with jok = [false] (see {!set_preconditioner}).

      @cvode <node5#sss:optout_spils> CVSpilsGetNumPrecEvals
    *)
    val get_num_prec_evals   : session -> int

    (**
      Returns the cumulative number of calls made to the preconditioner solve
      function, psolve (see {!set_preconditioner}).

      @cvode <node5#sss:optout_spils> CVSpilsGetNumPrecSolves
    *)
    val get_num_prec_solves  : session -> int

    (**
      Returns the cumulative number of calls made to the Jacobian-vector
      function, jtimes (see {! set_jac_times_vec_fn}).

      @cvode <node5#sss:optout_spils> CVSpilsGetNumJtimesEvals
    *)
    val get_num_jtimes_evals : session -> int

    (**
      Returns the number of calls to the user right-hand side function for
      finite difference Jacobian-vector product approximation. This counter is
      only updated if the default difference quotient function is used.

      @cvode <node5#sss:optout_spils> CVSpilsGetNumRhsEvals
    *)
    val get_num_rhs_evals    : session -> int
  end

(** {3 Banded preconditioner} *)

(** Get optional outputs for the banded preconditioner module of the
    Scaled Preconditioned Iterative Linear Solvers:
      SPGMR, SPBCG, SPTFQMR.
    @cvode <node5#sss:cvbandpre> Serial banded preconditioner module
  *)
module BandPrec :
  sig
    (** {4 Optional input functions} *)

    (**
      Returns the sizes of the real and integer workspaces used by the serial
      banded preconditioner module.

      @cvode <node5#sss:cvbandpre> CVBandPrecGetWorkSpace
      @return ([real_size], [integer_size])
     *)
    val get_work_space : session -> int * int

    (**
      Returns the number of calls made to the user-supplied right-hand side
      function due to finite difference banded Jacobian approximation in the
      banded preconditioner setup function.

      @cvode <node5#sss:cvbandpre> CVBandPrecGetNumRhsEvals
    *)
    val get_num_rhs_evals : session -> int
  end

