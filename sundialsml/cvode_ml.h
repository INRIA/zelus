/***********************************************************************
 *                                                                     *
 *              Ocaml interface to Sundials CVODE solver               *
 *                                                                     *
 *           Timothy Bourke (INRIA) and Marc Pouzet (LIENS)            *
 *                                                                     *
 *  Copyright 2013 Institut National de Recherche en Informatique et   *
 *  en Automatique.  All rights reserved.  This file is distributed    *
 *  under the terms of the GNU Library General Public License, with    *
 *  the special exception on linking described in file LICENSE.        *
 *                                                                     *
 ***********************************************************************/

/*
 * This module defines all constants and functions which do not depend on
 * the representation of continuous state vectors, i.e., those that are
 * shared between the bigarray and nvector versions of cvode_ml_nvec.
 *
 */

#ifndef _CVODE_ML_H__
#define _CVODE_ML_H__

/* Configuration options */
#define CHECK_MATRIX_ACCESS 1

void cvode_ml_check_flag(const char *call, int flag);

#define CHECK_FLAG(call, flag) if (flag != CV_SUCCESS) \
				 cvode_ml_check_flag(call, flag)


/*
 * The session data structure is shared in four parts across the OCaml and C
 * heaps:
 *
 *           C HEAP                   .           OCAML HEAP
 * -----------------------------------.---------------------------------
 *                                    .
 *                                    .            (Program using Sundials/ML)
 *                                    .                               |
 *                                    .       +--------------+        |
 *                             +---------+    | weak_hash_fn |        | 
 *                             | named   |    +--------------+        | 
 *  *_cvode_ml_get_session --->|  values +--->+ ~ ~ ~ ~ ~ ~  +---+    |
 *       (value *)             +---------+    +--------------+   |    |
 * "*_cvode_ml_get_session"           .                         \|/  \|/
 *                                    .                 +----------------+
 *                                    .                 |  session       |
 *                                    .                 +----------------+
 *             +----------------------------------------+ cvode          |
 *             |                      .                 | neqs           |
 *             |                      .                 | nroots         |
 *            \|/                     .                 | err_file       |
 *       +------------+               .                 | closure_rhsfn  |
 *       | cvode_mem  |               .                 | closure_rootfn |
 *       +------------+               .                 | ...            |
 *       |    ...     |               .                 +----------------+
 *       |cv_user_data| = weak_hash   .
 *       |    ...     |    key        .
 *       +------------+               .
 *				      .
 *
 *  * A cvode_mem structure is allocated by CVodeInit for each session. It
 *    is the "C side" of the session data structure.
 *
 *  * The "OCaml side" of the session data structure contains a pointer to
 *    a cvode_mem, several data fields, and the callback closures. It is
 *    returned to users of the library, and entered into a global array
 *    of weak pointers.
 *
 *  * The index of a session in the weak pointer array is stored in
 *    cvode_mem.cv_user_data. Callback routines pass this index to a
 *    *_cvode_ml_get_session function (ba_cvode_ml_get_session, or
 *    nvec_cvode_ml_get_session) to retrieve the session with its
 *    callbacks.
 *
 *    By linking through the weak_hash, we do not prevent a session from
 *    being reclamed when it is no longer needed. Callbacks are only
 *    activated as effects of functions that take a session value, thus
 *    guaranteeing that a cv_user_data index will always be valid.
 * 
 *  * The *_cvode_ml_get_session functions are registered as named values.
 *    Value pointers to the functions (value *) are cached in
 *    ba_cvode_ml_session_hash and nvec_cvode_ml_session_hash.
 *    The functions may be moved by the garbage collector, but the named
 *    value* is allocated in the C heap and does not move.
 *
 *  The init command:
 *  1. Calls CVodeInit to create a cvode_mem in the C heap.
 *  2. Returns this session paired with an initial value for err_file.
 *
 *  A finalizer is associated with session, on reclamation it:
 *  1. Calls CVodeFree to free cvode_mem.
 *  2. Closes session.err_file if necessary.
 * 
 *  The callback routines dereference and call "*_cvode_ml_*" routines which
 *  lookup a given session based on the index and call the appropriate
 *  function.
 */

void set_linear_solver(void *cvode_mem, value ls, int n);
value cvode_ml_big_real();

/* Interface with Ocaml types */

#define BIGARRAY_FLOAT (CAML_BA_FLOAT64 | CAML_BA_C_LAYOUT)
#define BIGARRAY_INT (CAML_BA_INT32 | CAML_BA_C_LAYOUT)

#define RECORD_SESSION_CVODE      0
#define RECORD_SESSION_USER_DATA  1
#define RECORD_SESSION_NEQS       2
#define RECORD_SESSION_NROOTS     3
#define RECORD_SESSION_ERRFILE    4
#define RECORD_SESSION_RHSFN      5
#define RECORD_SESSION_ROOTSFN    6
#define RECORD_SESSION_ERRH       7
#define RECORD_SESSION_ERRW       8
#define RECORD_SESSION_JACFN      9
#define RECORD_SESSION_BANDJACFN  10
#define RECORD_SESSION_PRESETUPFN 11
#define RECORD_SESSION_PRESOLVEFN 12
#define RECORD_SESSION_JACTIMESFN 13

#define CVODE_MEM_FROM_ML(v)       ((void *)Field((v), RECORD_SESSION_CVODE))
#define CVODE_USER_DATA_FROM_ML(v) \
    ((void *)(Long_val(Field((v), RECORD_SESSION_USER_DATA))))
#define CVODE_NEQS_FROM_ML(v)      Long_val(Field((v), RECORD_SESSION_NEQS))
#define CVODE_NROOTS_FROM_ML(v)    Long_val(Field((v), RECORD_SESSION_NROOTS))

#define VARIANT_LMM_ADAMS 0
#define VARIANT_LMM_BDF   1

#define RECORD_BANDRANGE_MUPPER 0
#define RECORD_BANDRANGE_MLOWER 1

#define RECORD_SPRANGE_PRETYPE 0
#define RECORD_SPRANGE_MAXL    1

/* untagged: */
#define VARIANT_LINEAR_SOLVER_DENSE	    0
#define VARIANT_LINEAR_SOLVER_LAPACKDENSE   1
#define VARIANT_LINEAR_SOLVER_DIAG	    2
/* tagged: */
#define VARIANT_LINEAR_SOLVER_BAND		    0
#define VARIANT_LINEAR_SOLVER_LAPACKBAND	    1
#define VARIANT_LINEAR_SOLVER_SPGMR		    2
#define VARIANT_LINEAR_SOLVER_SPBCG		    3
#define VARIANT_LINEAR_SOLVER_SPTFQMR		    4
#define VARIANT_LINEAR_SOLVER_BANDED_SPGMR	    5
#define VARIANT_LINEAR_SOLVER_BANDED_SPBCG	    6
#define VARIANT_LINEAR_SOLVER_BANDED_SPTFQMR	    7

#define VARIANT_SOLVER_RESULT_CONTINUE		0
#define VARIANT_SOLVER_RESULT_ROOTSFOUND	1
#define VARIANT_SOLVER_RESULT_STOPTIMEREACHED	2

#define RECORD_INTEGRATOR_STATS_STEPS			0
#define RECORD_INTEGRATOR_STATS_RHS_EVALS		1
#define RECORD_INTEGRATOR_STATS_LINEAR_SOLVER_SETUPS	2
#define RECORD_INTEGRATOR_STATS_ERROR_TEST_FAILURES	3
#define RECORD_INTEGRATOR_STATS_LAST_INTERNAL_ORDER	4
#define RECORD_INTEGRATOR_STATS_NEXT_INTERNAL_ORDER	5
#define RECORD_INTEGRATOR_STATS_INITIAL_STEP_SIZE	6
#define RECORD_INTEGRATOR_STATS_LAST_STEP_SIZE		7
#define RECORD_INTEGRATOR_STATS_NEXT_STEP_SIZE		8
#define RECORD_INTEGRATOR_STATS_INTERNAL_TIME		9

#define RECORD_ERROR_DETAILS_ERROR_CODE	    0
#define RECORD_ERROR_DETAILS_MODULE_NAME    1
#define RECORD_ERROR_DETAILS_FUNCTION_NAME  2
#define RECORD_ERROR_DETAILS_ERROR_MESSAGE  3

#define RECORD_JACOBIAN_ARG_JAC_T	0
#define RECORD_JACOBIAN_ARG_JAC_Y	1
#define RECORD_JACOBIAN_ARG_JAC_FY	2
#define RECORD_JACOBIAN_ARG_JAC_TMP	3

#define RECORD_SPILS_SOLVE_ARG_RHS	0
#define RECORD_SPILS_SOLVE_ARG_GAMMA	1
#define RECORD_SPILS_SOLVE_ARG_DELTA	2
#define RECORD_SPILS_SOLVE_ARG_LEFT	3

#define VARIANT_PRECOND_TYPE_PRECNONE	0
#define VARIANT_PRECOND_TYPE_PRECLEFT	1
#define VARIANT_PRECOND_TYPE_PRECRIGHT	2
#define VARIANT_PRECOND_TYPE_PRECBOTH	3

#define VARIANT_GRAMSCHMIDT_TYPE_MODIFIEDGS  0
#define VARIANT_GRAMSCHMIDT_TYPE_CLASSICALGS 1

#define VARIANT_PRECONDITIONING_TYPE_PRECNONE	0
#define VARIANT_PRECONDITIONING_TYPE_PRECLEFT	1
#define VARIANT_PRECONDITIONING_TYPE_PRECRIGHT	2
#define VARIANT_PRECONDITIONING_TYPE_PRECBOTH	3

#define VARIANT_GRAMSCHMIDT_TYPE_MODIFIEDGS	0
#define VARIANT_GRAMSCHMIDT_TYPE_CLASSICALGS	1

#endif

