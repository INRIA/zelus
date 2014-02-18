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

(** Vector-independent types and values for the CVODE solver.

 @version VERSION()
 @author Timothy Bourke (INRIA)
 @author Marc Pouzet (LIENS)
 *)

include module type of Sundials

(** {2 General} *)

(** {3 Solver initialisation} *)

(**
 Specify a linear multistep method.

 @cvode <node3#ss:ivp_sol> IVP Solution
 @cvode <node5#sss:cvodemalloc> CVodeCreate
 *)
type lmm =
  | Adams   (** Non-stiff systems; Adams-Moulton formulas *)
  | BDF     (** Stiff systems;     Backward Differentiation Formulas *)

(**
 Specify a solution method.

 @cvode <node3#ss:ivp_sol> IVP Solution
 @cvode <node5#sss:cvodemalloc> CVodeCreate
 *)
type iter =
  | Newton of linear_solver (** Newton iteration with a given linear solver *)
  | Functional              (** Functional iteration (non-stiff systems only) *)

(**
 Specify a linear solver.

 The Lapack solvers require that both Sundials and the Ocaml interface were
 built to link with a LAPACK library.

 The Banded Krylov solvers imply an additional call to
 {{:CVODE_DOC_ROOT(node5#sss:cvbandpre)} CVBandPrecInit}.

 @cvode <node5#sss:lin_solv_init> Linear Solver Specification
                                                 Functions
 *)
and linear_solver =
  | Dense                                   (** Direct with dense matrix,
                                                see {!Cvode_serial.Dls} and
                                                {!Cvode_nvector.Dls}.*)
  | LapackDense                             (** Direct with dense matrix,
                                                with Lapack,
                                                see {!Cvode_serial.Dls} and
                                                {!Cvode_nvector.Dls}.*)

  | Band of bandrange                       (** Direct with banded matrix,
                                                see {!Cvode_serial.Dls}
                                                and {!Cvode_nvector.Dls}.
                                             *)
  | LapackBand of bandrange                 (** Direct with banded matrix
                                                with Lapack,
                                                see {!Cvode_serial.Dls}
                                                and {!Cvode_nvector.Dls}.
                                             *)

  | Diag                                    (** Diagonal approximation
                                                of the Jacobian,
                                                see {!Cvode_serial.Diag}
                                                and {!Cvode_nvector.Diag}. *)

  | Spgmr of sprange                        (** Krylov Spils solver: SPGMR,
                                                see {!Cvode_serial.Spils}
                                                and {!Cvode_nvector.Spils}. *)
  | Spbcg of sprange                        (** Krylov Spils solver: SPBCG,
                                                see {!Cvode_serial.Spils}
                                                and {!Cvode_nvector.Spils}. *)
  | Sptfqmr of sprange                      (** Krylov Spils solver: SPFQMR,
                                                see {!Cvode_serial.Spils}
                                                and {!Cvode_nvector.Spils}. *)

  | BandedSpgmr of sprange * bandrange      (** Krylov Spils solver
                                                with banded matrix: SPGMR,
                                                see {!Cvode_serial.Spils},
                                                {!Cvode_serial.BandPrec},
                                                {!Cvode_nvector.Spils}, and
                                                {!Cvode_nvector.BandPrec}. *)
  | BandedSpbcg of sprange * bandrange      (** Krylov Spils solver
                                                with banded matrix: SPBCG,
                                                see {!Cvode_serial.Spils},
                                                {!Cvode_serial.BandPrec},
                                                {!Cvode_nvector.Spils}, and
                                                {!Cvode_nvector.BandPrec}. *)
  | BandedSptfqmr of sprange * bandrange    (** Krylov Spils solver
                                                with banded matrix: SPTFQMR,
                                                see {!Cvode_serial.Spils},
                                                {!Cvode_serial.BandPrec},
                                                {!Cvode_nvector.Spils}, and
                                                {!Cvode_nvector.BandPrec}. *)

(**
 @cvode <node5#sss:lin_solve_init> CVBand
 @cvode <node5#sss:cvbandpre> CVBandPrecInit
 *)
and bandrange = {
    mupper : int; (** upper half-bandwidth of the Jacobian approximation. *)
    mlower : int; (** lower half-bandwidth of the Jacobian approximation. *)
  }


(**
 Parameters for Krylov solvers.
 @cvode <node5#sss:lin_solv_init> CVSpgmr/CVSpbcg/CVSptfqrm
 *)
and sprange = {
    pretype : preconditioning_type;
    maxl: int
  }

(**
 Type of preconditioning for Krylov solvers.
 @cvode <node3#s:preconditioning> Preconditioning
 @cvode <node5#sss:lin_solv_init> CVSpgmr/CVSpbcg/CVSptfqrm
 *)
and preconditioning_type =
  | PrecNone
  | PrecLeft
  | PrecRight
  | PrecBoth

(**
 Values for root directions.
 @cvode <node5#sss:optin_root> CVodeSetRootDirection
 *)
type root_direction =
  | Increasing              (** Value changes from < 0 to >= 0 (+1) *)
  | Decreasing              (** Value changes from > 0 to <= 0 (-1) *)
  | IncreasingOrDecreasing  (** Increasing or Decreasing (0) *)

(**
 This is a convenience value for signalling to {!Cvode_serial.init} and
 {!Cvode_nvector.init} that there are no roots (zero-crossings) to
 monitor.
 *)
val no_roots : (int * ('a -> 'b -> 'c -> unit))

(** {3 Solver results, statistics, and errors} *)

(**
 Possible values returned when a solver step function succeeds.
 Failures are indicated by exceptions.

 @cvode <node5#sss:cvode> CVode
 *)
type solver_result =
  | Continue            (** CV_SUCCESS *)
  | RootsFound          (** CV_ROOT_RETURN *)
  | StopTimeReached     (** CV_TSTOP_RETURN *)

(**
 Aggregated integrator statistics.
 @cvode <node5#sss:optout_main> CVodeGetIntegratorStats
 *)
type integrator_stats = {
    num_steps : int;
    num_rhs_evals : int;
    num_lin_solv_setups : int;
    num_err_test_fails : int;
    last_order : int;
    current_order : int;
    actual_init_step : float;
    last_step : float;
    current_step : float;
    current_time : float
  }

(**
 Type of values passed to a registered error handler function.

 @cvode <node5#sss:optin_main> CVodeSetErrHandlerFn
 *)
type error_details = {
    error_code : int;
    module_name : string;
    function_name : string;
    error_message : string;
  }

(** {3:exceptions Exceptions} *)

(** @cvode <node5#sss:cvode> CV_ILL_INPUT *)
exception IllInput

(** @cvode <node5#sss:cvode> CV_TOO_CLOSE *)
exception TooClose

(** @cvode <node5#sss:cvode> CV_TOO_MUCH_WORK *)
exception TooMuchWork

(** @cvode <node5#sss:cvode> CV_TOO_MUCH_ACC *)
exception TooMuchAccuracy

(** @cvode <node5#sss:cvode> CV_ERR_FAIL *)
exception ErrFailure                

(** @cvode <node5#sss:cvode> CV_CONV_FAIL *)
exception ConvergenceFailure        

(** @cvode <node5#sss:cvode> CV_LINIT_FAIL *)
exception LinearInitFailure         

(** @cvode <node5#sss:cvode> CV_LSETUP_FAIL *)
exception LinearSetupFailure        

(** @cvode <node5#sss:cvode> CV_LSOLVE_FAIL *)
exception LinearSolveFailure        

(** @cvode <node5#sss:cvode> CV_RHSFUNC_FAIL *)
exception RhsFuncErr                

(** @cvode <node5#sss:cvode> CV_FIRST_RHSFUNC_FAIL *)
exception FirstRhsFuncFailure       

(** @cvode <node5#sss:cvode> CV_REPTD_RHSFUNC_ERR *)
exception RepeatedRhsFuncErr        

(** @cvode <node5#sss:cvode> CV_UNREC_RHSFUNC_ERR *)
exception UnrecoverableRhsFuncErr   

(** @cvode <node5#sss:cvode> CV_RTFUNC_FAIL *)
exception RootFuncFailure           

exception BadK      (** k is not in the range 0, 1, ..., q_u (CV_BAD_K)
                        @cvode <node5#ss:optional_dky> CVodeGetDky *)

exception BadT      (** t is not in the interval
                        \[t_n - h_u, t_n\] (CV_BAD_T)
                        @cvode <node5#ss:optional_dky> CVodeGetDky *)
exception BadDky    (** invalid dky argument (CV_BAD_DKY)
                        @cvode <node5#ss:optional_dky> CVodeGetDky *)

(**
 This exception may be thrown inside the RHS callback function (f)
 to indicate that one or more derivatives cannot be calculated at
 the given time offset. *)
exception RecoverableFailure


(**
 Thrown by the getrf functions if a zero diagonal element is encountered during
 factorization. The argument indicates the column index (from 1).

 @cvode <node9#ss:dense> DenseGETRF/denseGETRF 
 *)
exception ZeroDiagonalElement of int

(**
  {2 Data structures for Direct Linear Solvers}
  @cvode <node9#s:dls>  The DLS Modules
 *)

(** {3 Dense matrices}
    @cvode <node9#ss:dense> The DENSE Module *)

(** Operations for creating and manipulating dense matrices. *)
module Densematrix :
  sig
    (**
    This type represents a [DlsMat] returned from a call to
    {!new_dense_mat}.

     @cvode <node9#s:dls>  Type DlsMat
     @cvode <node9#ss:dense> NewDenseMat 
     *)
    type t

    (** {4 Basic access} *)

    (**
     [new_dense_mat m n] returns an [m] by [n]  dense matrix.

     @cvode <node9#ss:dense> NewDenseMat
     *)
    val new_dense_mat  : int * int -> t

    (**
     Prints a dense matrix to stdout.

     @cvode <node9#ss:dense> PrintMat
     *)
    val print_mat      : t -> unit

    (**
     [get a (i, j)] returns the value at row [i] and column [j] in [a],
     where [0 <= i < m] and [0 <= j < n].

     @cvode <node9#s:dls> DENSE_ELEM
     *)
    val get : t -> (int * int) -> float

    (**
     [set a (i, j) v] stores the value [v] at row [i] and column [j] in [a],
     where [0 <= i < m] and [0 <= j < n].

     @cvode <node9#s:dls> DENSE_ELEM
     *)
    val set : t -> (int * int) -> float -> unit

    (** {4 Calculations} *)

    (**
     Fills the matrix with zeros.

     @cvode <node9#ss:dense> SetToZero
     *)
    val set_to_zero    : t -> unit

    (**
     Increment a square matrix by the identity matrix.

     @cvode <node9#ss:dense> AddIdentity
     *)
    val add_identity   : t -> unit

    (**
     [copy src dst] copies the contents of one matrix into another.

     @cvode <node9#ss:dense> DenseCopy
     *)
    val copy     : t -> t -> unit

    (**
     [scale c a] multiplies each element of [a] by [c].

     @cvode <node9#ss:dense> DenseScale
     *)
    val scale    : float -> t -> unit

    (**
     [getrf a p] performs the LU factorization of [a] with partial pivoting
     according to [p].

     @cvode <node9#ss:dense> DenseGETRF
     @raise ZeroDiagonalElement Zero found in matrix diagonal
     *)
    val getrf    : t -> int_array -> unit

    (**
     [getrs a p b] finds the solution of [ax = b] using LU factorization.
     [a] must be a square matrix.

     @cvode <node9#ss:dense> DenseGETRS
     *)
    val getrs    : t -> int_array -> real_array -> unit

    (**
     Performs Cholesky factorization of a real symmetric positive matrix.

     @cvode <node9#ss:dense> DensePOTRF
     *)
    val potrf    : t -> unit

    (**
     [potrs a b] finds the solution of [ax = b] using Cholesky factorization.

     @cvode <node9#ss:dense> DensePOTRS
     *)
    val potrs    : t -> real_array -> unit

    (**
     [geqrf a beta work] performs the QR factorization of m by n matrix, with
     m >= n.

     @cvode <node9#ss:dense> DenseGEQRF
     *)
    val geqrf    : t -> real_array -> real_array -> unit

    (**
     [ormqr a beta v w work] computes the product [w = Qv], with Q calculated using {!geqrf}.

     @param a       matrix passed to {!geqrf}
     @param beta    vector apssed to {!geqrf}
     @param v       vector multiplier
     @param w       result vector
     @param work    temporary vector used in the calculation
     @cvode <node9#ss:dense> DenseORMQR
     *)
    val ormqr :
      a:t -> beta:real_array -> v:real_array -> w:real_array -> work:real_array -> unit

  end

(** {3 Direct dense matrices}
    @cvode <node9#ss:dense> The DENSE Module *)

(** Operations for creating and manipulating direct dense matrices. *)
module Directdensematrix :
  sig
    (**
     This type represents a [realtype **] returned from a call to
     {!new_dense_mat}.

     The underlying array cannot be exposed directly in Ocaml as a
     {{:OCAML_DOC_ROOT(Bigarray)} Bigarray} because it is an array of arrays
     (an lliffe vector) and, anyway, there is no simple way to attach a
     custom finalize function to such a big array.

     @cvode <node9#ss:dense> Small dense matrices
     @cvode <node9#ss:dense> newDenseMat 
     *)
    type t

    (** {4 Basic access} *)

    (**
     [new_dense_mat m n] returns an [m] by [n] dense small matrix.

     @cvode <node9#ss:dense> newDenseMat
     *)
    val new_dense_mat  : int * int -> t

    (**
     [get a (i, j)] returns the value at row [i] and column [j] in the m by
     n matrix [a], where 0 <= [i] < m and 0 <= [j] < n.
     *)
    val get : t -> (int * int) -> float

    (**
     [set a (i, j) v] stores the value [v] at row [i] and column [j] in the
     m by n matrix [a], where 0 <= [i] < m and 0 <= [j] < n.
     *)
    val set : t -> (int * int) -> float -> unit

    (** {4 Calculations} *)

    (**
     [copy src dst (m, n)] copies the contents of one [m] by [n] matrix
     into another.

     @cvode <node9#ss:dense> denseCopy
     *)
    val copy  : t -> t -> int * int -> unit

    (*
     [scale c a (m, n)] multiplies each element of the [m] by [n]
     matrix [a] by [c].

     @cvode <node9#ss:dense> denseScale
     *)
    val scale : float -> t -> int * int -> unit

    (**
     [add_identity a n] increments an [n] by [n] matrix by the identity
     matrix.

     @cvode <node9#ss:dense> denseAddIdentity
     *)
    val add_identity : t -> int -> unit

    (**
     [getrf a (m, n) p] performs the LU factorization of an [m] by [n] matrix
     [a] with partial pivoting according to [p].

     @cvode <node9#ss:dense> denseGETRF
     @raise ZeroDiagonalElement Zero found in matrix diagonal
     *)
    val getrf : t -> int * int -> int_array -> unit

    (**
     [getrs a n p b] finds the solution of [ax = b] using LU factorization.
     [a] must be an [n] by [n]  matrix.

     @cvode <node9#ss:dense> denseGETRS
     *)
    val getrs : t -> int -> int_array -> real_array -> unit

    (**
     [potrf a n] performs the Cholesky factorization of a real symmetric positive
     [n] by [n] matrix.

     @cvode <node9#ss:dense> DensePOTRF
     @cvode <node9#ss:dense> densePOTRF
     *)
    val potrf : t -> int -> unit

    (**
     [potrs a n b] finds the solution of [ax = b] using Cholesky
     factorization. [a] must be an [n] by [n] matrix.

     @cvode <node9#ss:dense> densePOTRS
     *)
    val potrs : t -> int -> real_array -> unit

    (**
     [geqrf a (m, n) beta work] performs the QR factorization of an
     [m] by [n] matrix, where [m] >= [n].

     @cvode <node9#ss:dense> denseGEQRF
     *)
    val geqrf : t -> int * int -> real_array -> real_array -> unit

    (**
     [ormqr a beta v w work] computes the product [w = Qv], with Q calculated using {!geqrf}.

     @param a       matrix passed to {!geqrf}
     @param beta    vector apssed to {!geqrf}
     @param v       vector multiplier
     @param w       result vector
     @param work    temporary vector used in the calculation
     @cvode <node9#ss:dense> denseORMQR
     *)
    val ormqr :
      a:t -> mn:(int * int)
      -> beta:real_array -> v:real_array -> w:real_array -> work:real_array
      -> unit
  end

(** {3 Banded matrices}
    @cvode <node9#ss:band> The BAND Module *)

(** Operations for creating and manipulating banded matrices. *)
module Bandmatrix :
  sig
    (**
    This type represents a [DlsMat] returned from a call to
    {!new_band_mat}.

     @cvode <node9#s:dls>  Type DlsMat
     @cvode <node9#ss:band> NewBandMat 
     *)
    type t

    (** {4 Basic access} *)

    (**
     [new_band_mat n mu ml smu] returns an [n] by [n] band matrix of upper
     bandwith [mu] and lower bandwidth [ml].
     - If [smu] = [mu], the result will {b not} be LU factored.
     - Otherwise pass [smu] = min([n]-1, [mu] + [ml]).

     @cvode <node9#ss:band> NewBandMat
     *)
    val new_band_mat : int * int * int * int -> t

    (**
     Prints a band matrix to stdout.

     @cvode <node9#ss:band> PrintMat
     *)
    val print_mat : t -> unit

    (**
     [get a (i, j)] returns the value at row [i] and column [j] of the n by n
     matrix [a],
     where 0 <= [i], [j] <= n - 1 and [j] - mu(A) <= [i] <= [j] + ml(A).

     @cvode <node9#s:dls> BAND_ELEM
     *)
    val get : t -> (int * int) -> float

    (**
      [set a (i, j) v] stores the value [v] at row [i] and column [j] of the
      n by n matrix [a], where 0 <= [i], [j] <= n - 1 and
      [j] - mu(A) <= [i] <= [j] + ml(A).

      @cvode <node9#s:dls> BAND_ELEM
     *)
    val set : t -> (int * int) -> float -> unit

    (** {4 Calculations} *)

    (**
     Fills the matrix with zeros.

     @cvode <node9#ss:band> SetToZero
     *)
    val set_to_zero    : t -> unit

    (**
     Increment a square matrix by the identity matrix.

     @cvode <node9#ss:band> AddIdentity
     *)
    val add_identity   : t -> unit

    (**
     [copy src dst copymu copyml] copies the submatrix with upper and lower
     bandwidths [copymu] and [copyml] of the n by n band matrix [src] into the n
     by n band matrix [dst].

     @cvode <node9#ss:band> BandCopy
     *)
    val copy : t -> t -> int -> int -> unit

    (**
     [scale c a] multiplies each element of [a] by [c].

     @cvode <node9#ss:band> BandScale
     *)
    val scale : float -> t -> unit

    (**
     [gbtrf a p] performs the LU factorization of [a] with partial pivoting
     according to [p].

     @cvode <node9#ss:band> BandGBTRF
     *)
    val gbtrf : t -> int_array -> unit

    (**
     [gbtrs a p b] finds the solution of [ax = b] using LU factorization.
     [a] must be a square matrix.

     @cvode <node9#ss:band> BandGBTRS
     *)
    val gbtrs : t -> int_array -> real_array -> unit

    (** {4 Column access} *)

    (** Access banded matrix columns *)
    module Col :
      sig
        (**
         This type represents a bandmatrix ([DlsMat]) column.

         The underlying array cannot be exposed directly in Ocaml as a
         {{:OCAML_DOC_ROOT(Bigarray)} Bigarray} because there is no simple way
         to attach a custom finalize function to such a big array.

         @cvode <node9#s:dls> BAND_COL
         *)
        type c

        (**
         [get_col a j] returns the diagonal element of the j-th column of the n
         by n band matrix [a], where 0 <= [j] <= n - 1.
         The resulting column may be indexed from -mu([a]) to ml([a]).

         @cvode <node9#s:dls> BAND_COL
         *)
        val get_col : t -> int -> c

        (**
         [get c (i, j)] returns the ([i], [j])th entry of the band matrix from
         which the column [c] has already been selected;
         provided that [j] - mu(c) <= [i] <= [j] + ml(c).

         @cvode <node9#s:dls> BAND_COL_ELEM
         *)
        val get : c -> (int * int) -> float

        (**
         [set c (i, j) v] stores the value [v] at the ([i], [j])th entry of
         the band matrix from which the column [c] has already been selected;
         provided that [j] - mu(c) <= [i] <= [j] + ml(c).

         @cvode <node9#s:dls> BAND_COL_ELEM
         *)
        val set : c -> (int * int) -> float -> unit
      end
  end

(** {3 Direct banded matrices}
    @cvode <node9#ss:band> The BAND Module *)

(** Operations for creating and manipulating direct banded matrices. *)
module Directbandmatrix :
  sig
    (**
     This type represents a [realtype **] returned from a call to
     {!new_band_mat}.

     The underlying array cannot be exposed directly in Ocaml as a
     {{:OCAML_DOC_ROOT(Bigarray)} Bigarray} because it is an array of arrays
     (an lliffe vector) and, anyway, there is no simple way to attach a
     custom finalize function to such a big array.

     @cvode <node9#ss:band> NewBandMat 
     *)
    type t

    (** {4 Basic access} *)

    (**
     [new_band_mat n smu ml] returns an [n] by [n] band matrix with lower
     half-bandwidth [ml].

     @cvode <node9#ss:band> newBandMat
     *)
    val new_band_mat : int * int * int -> t

    (**
     [get a (i, j)] returns the value at row [i] and column [j] in the m by
     n matrix [a], where 0 <= [i] < m and 0 <= [j] < n.
     *)
    val get : t -> (int * int) -> float

    (**
     [set a (i, j) v] stores the value [v] at row [i] and column [j] in the
     m by n matrix [a], where 0 <= [i] < m and 0 <= [j] < n.
     *)
    val set : t -> (int * int) -> float -> unit

    (** {4 Calculations} *)

    (**
     [copy src dst n a_smu b_smu copymu copyml] copies the submatrix with
     upper and lower bandwidths [copymu] and [copyml] of the [n] by [n] band
     matrix [src] into the [n] by [n] band matrix [dst].

     @cvode <node9#ss:band> bandCopy
     *)
    val copy : t -> t -> int -> int -> int -> int -> int -> unit

    (**
     [scale c a n mu ml smu] multiplies each element of the [n] by [n] band
     matrix [a], having bandwidths [mu] and [ml], by [c].

     @cvode <node9#ss:band> bandScale
     *)
    val scale : float -> t -> int -> int -> int -> int -> unit

    (**
     [add_idenity a n smu] increments the [n] by [n]  matrix [a] by the
     identity matrix.

     @cvode <node9#ss:band> bandAddIdentity
     *)
    val add_identity : t -> int -> int -> unit

    (**
     [gbtrf a n mu ml smu p] performs the LU factorization of the [n] by [n]
     band matrix [a], having bandwidths [mu] and [ml], with partial pivoting
     according to [p].

     @cvode <node9#ss:band> bandGBTRF
     *)
    val gbtrf : t -> int -> int -> int -> int -> int_array -> unit

    (**
     [gbtrs a n smu ml p b] finds the solution of [ax = b] using LU factorization.
     [a] must be an [n] by [n]  matrix having bandwidths [mu] and [ml].

     @cvode <node9#ss:band> bandGBTRS
     *)
    val gbtrs
        : t -> int -> int -> int -> int_array -> real_array -> unit
  end
