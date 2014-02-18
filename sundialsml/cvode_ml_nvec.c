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

/* The parts of the Sundials interface that distinguish between Serial
   NVectors (handled by Bigarrays) and generic NVectors (handled by a
   wrapper type). */

#include <cvode/cvode.h>
#include <sundials/sundials_config.h>
#include <sundials/sundials_types.h>

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/unixsupport.h>
#include <caml/bigarray.h>

/* linear solvers */
#include <cvode/cvode_dense.h>
#include <cvode/cvode_band.h>
#include <cvode/cvode_diag.h>
#include <cvode/cvode_spgmr.h>
#include <cvode/cvode_spbcgs.h>
#include <cvode/cvode_sptfqmr.h>
#include <cvode/cvode_bandpre.h>

#include "cvode_ml.h"
#include "nvector_ml.h"

#ifdef RESTRICT_INTERNAL_PRECISION
#ifdef __GNUC__
#include <fpu_control.h>
#endif
#endif

// Call with CVODE_ML_BIGARRAYS to compile for the Serial NVector to
// Bigarray interface code.

#ifdef CVODE_ML_BIGARRAYS

#define CVTYPE(fname) c_ba_ ## fname
#include <nvector/nvector_serial.h>

#define WRAP_NVECTOR(v) caml_ba_alloc(BIGARRAY_FLOAT, 1, NV_DATA_S(v), &(NV_LENGTH_S(v)))
#define RELINQUISH_WRAPPEDNV(v_ba) Caml_ba_array_val(v_ba)->dim[0] = 0

#define NVECTORIZE_VAL(ba) N_VMake_Serial(Caml_ba_array_val(ba)->dim[0], (realtype *)Caml_ba_data_val(ba))
#define RELINQUISH_NVECTORIZEDVAL(nv) N_VDestroy(nv)

#else

#define CVTYPE(fname) c_nvec_ ## fname
#include <sundials/sundials_nvector.h>

#define WRAP_NVECTOR(v) NVEC_DATA(v)
#define RELINQUISH_WRAPPEDNV(v) {}

#define NVECTORIZE_VAL(v) NVEC_VAL(v)
#define RELINQUISH_NVECTORIZEDVAL(nv) {}

#endif

#define DOQUOTE(text) #text
#define QUOTE(val) DOQUOTE(val)
#define CVTYPESTR(fname) QUOTE(CVTYPE(fname))

/* callbacks */

static void errh(
	int error_code,
	const char *module,
	const char *func,
	char *msg,
	void *eh_data)
{
    CAMLparam0();
    CAMLlocal1(a);

    static value *cvode_ml_errh;
    if (cvode_ml_errh == NULL)
	cvode_ml_errh = caml_named_value(CVTYPESTR(cvode_ml_errh));

    a = caml_alloc_tuple(4);
    Store_field(a, RECORD_ERROR_DETAILS_ERROR_CODE, Val_int(error_code));
    Store_field(a, RECORD_ERROR_DETAILS_MODULE_NAME, caml_copy_string(module));
    Store_field(a, RECORD_ERROR_DETAILS_FUNCTION_NAME, caml_copy_string(func));
    Store_field(a, RECORD_ERROR_DETAILS_ERROR_MESSAGE, caml_copy_string(msg));

    caml_callback2(*cvode_ml_errh, Val_long((long int)eh_data), a);

    CAMLreturn0;
}

CAMLprim void CVTYPE(set_err_handler_fn)(value vdata)
{
    CAMLparam1(vdata);
 
    int flag = CVodeSetErrHandlerFn(CVODE_MEM_FROM_ML(vdata), errh,
				    CVODE_USER_DATA_FROM_ML(vdata));
    CHECK_FLAG("CVodeSetErrHandlerFn", flag);

    CAMLreturn0;
}

CAMLprim void CVTYPE(clear_err_handler_fn)(value vdata)
{
    CAMLparam1(vdata);

    int flag = CVodeSetErrHandlerFn(CVODE_MEM_FROM_ML(vdata), NULL, NULL);
    CHECK_FLAG("CVodeSetErrHandlerFn", flag);

    CAMLreturn0;
}


static int check_exception(value r)
{
    CAMLparam1(r);
    CAMLlocal1(exn);

    static value *recoverable_failure = NULL;

    if (!Is_exception_result(r)) return 0;

    if (recoverable_failure == NULL) {
	recoverable_failure =
	    caml_named_value("cvode_RecoverableFailure");
    }

    exn = Extract_exception(r);
    CAMLreturn((Field(exn, 0) == *recoverable_failure) ? 1 : -1);
}

static int f(realtype t, N_Vector y, N_Vector ydot, void *user_data)
{
    CAMLparam0();
    CAMLlocal1(r);
    CAMLlocalN(args, 4);

    static value *cvode_ml_rhsfn;
    if (cvode_ml_rhsfn == NULL)
	cvode_ml_rhsfn = caml_named_value(CVTYPESTR(cvode_ml_rhsfn));

    args[0] = Val_long((long int)user_data);
    args[1] = caml_copy_double(t);
    args[2] = WRAP_NVECTOR(y);
    args[3] = WRAP_NVECTOR(ydot);

    // the data payloads inside y_d (args[2]) and ydot_d (args[3]) are only
    // valid during this call, afterward that memory goes back to cvode.
    // These bigarrays must not be retained by closure_rhsfn! If it wants a
    // permanent copy, then it has to make it manually.
    r = caml_callbackN_exn(*cvode_ml_rhsfn, 4, args);

    RELINQUISH_WRAPPEDNV(args[2]);
    RELINQUISH_WRAPPEDNV(args[3]);

    CAMLreturn(check_exception(r));
}

static int roots(realtype t, N_Vector y, realtype *gout, void *user_data)
{
    CAMLparam0();
    CAMLlocal4(session, r, vy, roots);

    static value *cvode_ml_session;
    if (cvode_ml_session == NULL)
	cvode_ml_session = caml_named_value(CVTYPESTR(cvode_ml_session));

    session = caml_callback(*cvode_ml_session, Val_long((long int)user_data));
    intnat nroots = CVODE_NROOTS_FROM_ML(session);

    vy = WRAP_NVECTOR(y);
    roots = caml_ba_alloc(BIGARRAY_FLOAT, 1, gout, &nroots);

    // see notes for f()
    r = caml_callback3_exn(Field(session, RECORD_SESSION_ROOTSFN),
			   caml_copy_double(t), vy, roots);

    RELINQUISH_WRAPPEDNV(vy);
    Caml_ba_array_val(roots)->dim[0] = 0;

    CAMLreturn(check_exception(r));
}

static int errw(N_Vector y, N_Vector ewt, void *user_data)
{
    CAMLparam0();
    CAMLlocal3(y_d, ewt_d, r);

    static value *cvode_ml_errw;
    if (cvode_ml_errw == NULL)
	cvode_ml_errw = caml_named_value(CVTYPESTR(cvode_ml_errw));

    y_d = WRAP_NVECTOR(y);
    ewt_d = WRAP_NVECTOR(ewt);

    // see notes for f()
    r = caml_callback3_exn(*cvode_ml_errw, Val_long((long int)user_data),
			   y_d, ewt_d);

    RELINQUISH_WRAPPEDNV(y_d);
    RELINQUISH_WRAPPEDNV(ewt_d);

    CAMLreturn(check_exception(r));
}

static value make_jac_arg(realtype t, N_Vector y, N_Vector fy, value tmp)
{
    CAMLparam0();
    CAMLlocal1(r);

    r = caml_alloc_tuple(4);
    Store_field(r, RECORD_JACOBIAN_ARG_JAC_T, caml_copy_double(t));
    Store_field(r, RECORD_JACOBIAN_ARG_JAC_Y, WRAP_NVECTOR(y));
    Store_field(r, RECORD_JACOBIAN_ARG_JAC_FY, WRAP_NVECTOR(fy));
    Store_field(r, RECORD_JACOBIAN_ARG_JAC_TMP, tmp);

    CAMLreturn(r);
}

static value make_triple_tmp(N_Vector tmp1, N_Vector tmp2, N_Vector tmp3)
{
    CAMLparam0();
    CAMLlocal1(r);

    r = caml_alloc_tuple(3);
    Store_field(r, 0, WRAP_NVECTOR(tmp1));
    Store_field(r, 1, WRAP_NVECTOR(tmp2));
    Store_field(r, 2, WRAP_NVECTOR(tmp3));
    CAMLreturn(r);
}

static void relinquish_jac_arg(value arg, int triple)
{
    CAMLparam0();
    CAMLlocal1(tmp);

    RELINQUISH_WRAPPEDNV(Field(arg, RECORD_JACOBIAN_ARG_JAC_Y));
    RELINQUISH_WRAPPEDNV(Field(arg, RECORD_JACOBIAN_ARG_JAC_FY));

    tmp = Field(arg, RECORD_JACOBIAN_ARG_JAC_TMP);

    if (triple) {
	RELINQUISH_WRAPPEDNV(Field(tmp, 0));
	RELINQUISH_WRAPPEDNV(Field(tmp, 1));
	RELINQUISH_WRAPPEDNV(Field(tmp, 2));
    } else {
	RELINQUISH_WRAPPEDNV(tmp);
    }

    CAMLreturn0;
}

static int jacfn(
	int n,
	realtype t,
	N_Vector y,
	N_Vector fy,	     
	DlsMat Jac,
	void *user_data,
	N_Vector tmp1,
	N_Vector tmp2,
	N_Vector tmp3)
{
    CAMLparam0();
    CAMLlocal3(arg, vjac, r);

    static value *cvode_ml_jacfn;
    if (cvode_ml_jacfn == NULL)
	cvode_ml_jacfn = caml_named_value(CVTYPESTR(cvode_ml_jacfn));

    arg = make_jac_arg(t, y, fy, make_triple_tmp(tmp1, tmp2, tmp3));

    vjac = caml_alloc_final(2, NULL, 0, 1);
    Store_field(vjac, 1, (value)Jac);

    r = caml_callback3_exn(*cvode_ml_jacfn, Val_long((long int)user_data),
			   arg, vjac);
    relinquish_jac_arg(arg, 1);
    // note: matrix is also invalid after the callback

    CAMLreturn(check_exception(r));
}

static int bandjacfn(
	int N,
	int mupper,
	int mlower, 	 
	realtype t,
	N_Vector y,
	N_Vector fy, 	 
	DlsMat Jac,
	void *user_data, 	 
	N_Vector tmp1,
	N_Vector tmp2,
	N_Vector tmp3)
{
    CAMLparam0();
    CAMLlocal2(r, vjac);
    CAMLlocalN(args, 5);

    static value *cvode_ml_bandjacfn;
    if (cvode_ml_bandjacfn == NULL)
	cvode_ml_bandjacfn = caml_named_value(CVTYPESTR(cvode_ml_bandjacfn));

    vjac = caml_alloc_final(2, NULL, 0, 1);
    Store_field(vjac, 1, (value)Jac);

    args[0] = Val_long((long int)user_data);
    args[1] = make_jac_arg(t, y, fy, make_triple_tmp(tmp1, tmp2, tmp3));
    args[2] = Val_int(mupper);
    args[3] = Val_int(mlower);
    args[4] = vjac;

    r = caml_callbackN_exn(*cvode_ml_bandjacfn, 5, args);

    relinquish_jac_arg(args[1], 1);
    // note: args[4] is also invalid after the callback

    CAMLreturn(check_exception(r));
}

static int presetupfn(
    realtype t,
    N_Vector y,
    N_Vector fy,
    booleantype jok,
    booleantype *jcurPtr,
    realtype gamma,
    void *user_data,
    N_Vector tmp1,
    N_Vector tmp2,
    N_Vector tmp3)
{
    CAMLparam0();
    CAMLlocal1(r);
    CAMLlocalN(args, 4);

    static value *cvode_ml_presetupfn;
    if (cvode_ml_presetupfn == NULL)
	cvode_ml_presetupfn = caml_named_value(CVTYPESTR(cvode_ml_presetupfn));

    args[0] = Val_long((long int)user_data);
    args[1] = make_jac_arg(t, y, fy, make_triple_tmp(tmp1, tmp2, tmp3));
    args[2] = Val_bool(jok);
    args[3] = caml_copy_double(gamma);

    r = caml_callbackN_exn(*cvode_ml_presetupfn, 4, args);

    relinquish_jac_arg(args[1], 1);

    if (!Is_exception_result(r)) {
	*jcurPtr = Bool_val(r);
    }

    CAMLreturn(check_exception(r));
}

static value make_spils_solve_arg(
	N_Vector r,
	realtype gamma,
	realtype delta,
	int lr)

{
    CAMLparam0();
    CAMLlocal1(v);

    v = caml_alloc_tuple(4);
    Store_field(v, RECORD_SPILS_SOLVE_ARG_RHS, WRAP_NVECTOR(r));
    Store_field(v, RECORD_SPILS_SOLVE_ARG_GAMMA, caml_copy_double(gamma));
    Store_field(v, RECORD_SPILS_SOLVE_ARG_DELTA, caml_copy_double(delta));
    Store_field(v, RECORD_SPILS_SOLVE_ARG_LEFT, lr == 1 ? Val_true : Val_false);

    CAMLreturn(v);
}

static CAMLprim void relinquish_spils_solve_arg(value arg)
{
    CAMLparam0();
    RELINQUISH_WRAPPEDNV(Field(arg, RECORD_SPILS_SOLVE_ARG_RHS));
    CAMLreturn0;
}

static int presolvefn(
	realtype t,
	N_Vector y,
	N_Vector fy,
	N_Vector r,
	N_Vector z,
	realtype gamma,
	realtype delta,
	int lr,
	void *user_data,
	N_Vector tmp)
{
    CAMLparam0();
    CAMLlocal1(rv);
    CAMLlocalN(args, 4);

    static value *cvode_ml_presolvefn;
    if (cvode_ml_presolvefn == NULL)
	cvode_ml_presolvefn = caml_named_value(CVTYPESTR(cvode_ml_presolvefn));

    args[0] = Val_long((long int)user_data);
    args[1] = make_jac_arg(t, y, fy, WRAP_NVECTOR(tmp));
    args[2] = make_spils_solve_arg(r, gamma, delta, lr);
    args[3] = WRAP_NVECTOR(z);

    rv = caml_callbackN_exn(*cvode_ml_presolvefn, 4, args);

    relinquish_jac_arg(args[1], 0);
    relinquish_spils_solve_arg(args[2]);
    RELINQUISH_WRAPPEDNV(args[3]);

    CAMLreturn(check_exception(rv));
}

static int jactimesfn(
    N_Vector v,
    N_Vector Jv,
    realtype t,
    N_Vector y,
    N_Vector fy,
    void *user_data,
    N_Vector tmp)
{
    CAMLparam0();
    CAMLlocal1(r);
    CAMLlocalN(args, 4);

    static value *cvode_ml_jactimesfn;
    if (cvode_ml_jactimesfn == NULL)
	cvode_ml_jactimesfn = caml_named_value(CVTYPESTR(cvode_ml_jactimesfn));

    args[0] = Val_long((long int)user_data);
    args[1] = make_jac_arg(t, y, fy, WRAP_NVECTOR(tmp));
    args[2] = WRAP_NVECTOR(v);
    args[3] = WRAP_NVECTOR(Jv);

    r = caml_callbackN_exn(*cvode_ml_jactimesfn, 4, args);

    relinquish_jac_arg(args[1], 0);
    RELINQUISH_WRAPPEDNV(args[2]);
    RELINQUISH_WRAPPEDNV(args[3]);

    CAMLreturn(check_exception(r));
}

CAMLprim void CVTYPE(wf_tolerances)(value vdata)
{
    CAMLparam1(vdata);
 
    int flag = CVodeWFtolerances(CVODE_MEM_FROM_ML(vdata), errw);
    CHECK_FLAG("CVodeWFtolerances", flag);

    CAMLreturn0;
}

CAMLprim void CVTYPE(dls_set_dense_jac_fn)(value vdata)
{
    CAMLparam1(vdata);
    int flag = CVDlsSetDenseJacFn(CVODE_MEM_FROM_ML(vdata), jacfn);
    CHECK_FLAG("CVDlsSetDenseJacFn", flag);
    CAMLreturn0;
}

CAMLprim void CVTYPE(dls_clear_dense_jac_fn)(value vdata)
{
    CAMLparam1(vdata);
    int flag = CVDlsSetDenseJacFn(CVODE_MEM_FROM_ML(vdata), NULL);
    CHECK_FLAG("CVDlsSetDenseJacFn", flag);
    CAMLreturn0;
}

CAMLprim void CVTYPE(dls_set_band_jac_fn)(value vdata, value fbandjacfn)
{
    CAMLparam1(vdata);
    int flag = CVDlsSetBandJacFn(CVODE_MEM_FROM_ML(vdata), bandjacfn);
    CHECK_FLAG("CVDlsSetBandJacFn", flag);
    CAMLreturn0;
}

CAMLprim void CVTYPE(dls_clear_band_jac_fn)(value vdata)
{
    CAMLparam1(vdata);
    int flag = CVDlsSetBandJacFn(CVODE_MEM_FROM_ML(vdata), NULL);
    CHECK_FLAG("CVDlsSetBandJacFn", flag);
    CAMLreturn0;
}

CAMLprim void CVTYPE(set_preconditioner)(value vdata)
{
    CAMLparam1(vdata);
    int flag = CVSpilsSetPreconditioner(CVODE_MEM_FROM_ML(vdata),
					presetupfn, presolvefn);
    CHECK_FLAG("CVSpilsSetPreconditioner", flag);
    CAMLreturn0;
}

CAMLprim void CVTYPE(set_jac_times_vec_fn)(value vdata)
{
    CAMLparam1(vdata);
    int flag = CVSpilsSetJacTimesVecFn(CVODE_MEM_FROM_ML(vdata), jactimesfn);
    CHECK_FLAG("CVSpilsSetJacTimesVecFn", flag);
    CAMLreturn0;
}

CAMLprim void CVTYPE(clear_jac_times_vec_fn)(value vdata)
{
    CAMLparam1(vdata);
    int flag = CVSpilsSetJacTimesVecFn(CVODE_MEM_FROM_ML(vdata), NULL);
    CHECK_FLAG("CVSpilsSetJacTimesVecFn", flag);
    CAMLreturn0;
}

/* basic interface */

CAMLprim value CVTYPE(init)(value lmm, value iter, value initial,
			    value num_eqs, value num_roots, value t0)
{
    CAMLparam5(lmm, iter, initial, num_eqs, num_roots);
    CAMLxparam1(t0);
    CAMLlocal1(r);

    if (sizeof(int) != 4) {
	caml_failwith("The library assumes that an int (in C) has 32-bits.");
    }

#ifdef RESTRICT_INTERNAL_PRECISION
#ifdef __GNUC__
    fpu_control_t fpu_cw;
    _FPU_GETCW(fpu_cw);
    fpu_cw = (fpu_cw & ~_FPU_EXTENDED & ~_FPU_SINGLE) | _FPU_DOUBLE;
    _FPU_SETCW(fpu_cw);
#endif
#endif

    int flag;

    int lmm_c;
    switch (Int_val(lmm)) {
    case VARIANT_LMM_ADAMS:
	lmm_c = CV_ADAMS;
	break;

    case VARIANT_LMM_BDF:
	lmm_c = CV_BDF;
	break;

    default:
	caml_failwith("Illegal lmm value.");
	break;
    }

    int iter_c;
    if (Is_block(iter)) {
	iter_c = CV_NEWTON;
    } else {
	iter_c = CV_FUNCTIONAL;
    }

    void *cvode_mem = CVodeCreate(lmm_c, iter_c);
    if (cvode_mem == NULL)
	caml_failwith("CVodeCreate returned NULL");

    long int neq = Long_val(num_eqs);
    intnat nroots = Int_val(num_roots);

    N_Vector initial_nv = NVECTORIZE_VAL(initial);
    flag = CVodeInit(cvode_mem, f, Double_val(t0), initial_nv);
    RELINQUISH_NVECTORIZEDVAL(initial_nv);
    CHECK_FLAG("CVodeInit", flag);

    if (nroots > 0) {
	flag = CVodeRootInit(cvode_mem, nroots, roots);
	if (flag != CV_SUCCESS) {
	    CVodeFree(cvode_mem);
	    cvode_ml_check_flag("CVodeRootInit", flag);
	}
    }

    // setup linear solvers (if necessary)
    if (iter_c == CV_NEWTON) {
	set_linear_solver(cvode_mem, Field(iter, 0), neq);
    }

    // default tolerances
    flag = CVodeSStolerances(cvode_mem, RCONST(1.0e-4), RCONST(1.0e-8));
    if (flag != CV_SUCCESS) {
	CVodeFree(cvode_mem);
	cvode_ml_check_flag("CVodeSStolerances", flag);
    }

    r = caml_alloc_tuple(2);
    Store_field(r, 0, (value)cvode_mem);
    Store_field(r, 1, Val_long(0)); // no err_file = NULL

    CAMLreturn(r);
}

CAMLprim value CVTYPE(init_bytecode)(value *tbl, int n)
{
    return CVTYPE(init)(tbl[0], tbl[1], tbl[2], tbl[3], tbl[4], tbl[5]);
}

CAMLprim void CVTYPE(sv_tolerances)(value vdata, value reltol, value abstol)
{
    CAMLparam3(vdata, reltol, abstol);

    N_Vector atol_nv = NVECTORIZE_VAL(abstol);

    int flag = CVodeSVtolerances(CVODE_MEM_FROM_ML(vdata),
				 Double_val(reltol), atol_nv);
    RELINQUISH_NVECTORIZEDVAL(atol_nv);
    CHECK_FLAG("CVodeSVtolerances", flag);

    CAMLreturn0;
}

CAMLprim void CVTYPE(reinit)(value vdata, value t0, value y0)
{
    CAMLparam3(vdata, t0, y0);

    N_Vector y0_nv = NVECTORIZE_VAL(y0);
    int flag = CVodeReInit(CVODE_MEM_FROM_ML(vdata), Double_val(t0), y0_nv);
    RELINQUISH_NVECTORIZEDVAL(y0_nv);
    CHECK_FLAG("CVodeReInit", flag);

    CAMLreturn0;
}

static value solver(value vdata, value nextt, value y, int onestep)
{
    CAMLparam3(vdata, nextt, y);
    CAMLlocal1(r);

    realtype t = 0.0;
    N_Vector y_nv = NVECTORIZE_VAL(y);

    // The payload of y (a big array) must not be shifted by the Ocaml GC
    // during this function call, even though Caml will be reentered
    // through the callback f. Is this guaranteed?
    int flag = CVode(CVODE_MEM_FROM_ML(vdata), Double_val(nextt), y_nv, &t,
		     onestep ? CV_ONE_STEP : CV_NORMAL);
    RELINQUISH_NVECTORIZEDVAL(y_nv);
    CHECK_FLAG("CVode", flag);

    r = caml_alloc_tuple(2);
    Store_field(r, 0, caml_copy_double(t));

    switch (flag) {
    case CV_ROOT_RETURN:
	Store_field(r, 1, Val_int(VARIANT_SOLVER_RESULT_ROOTSFOUND));
	break;

    case CV_TSTOP_RETURN:
	Store_field(r, 1, Val_int(VARIANT_SOLVER_RESULT_STOPTIMEREACHED));
	break;

    default:
	Store_field(r, 1, Val_int(VARIANT_SOLVER_RESULT_CONTINUE));
    }

    CAMLreturn(r);
}

CAMLprim value CVTYPE(normal)(value vdata, value nextt, value y)
{
    CAMLparam3(vdata, nextt, y);
    CAMLreturn(solver(vdata, nextt, y, 0));
}

CAMLprim value CVTYPE(one_step)(value vdata, value nextt, value y)
{
    CAMLparam3(vdata, nextt, y);
    CAMLreturn(solver(vdata, nextt, y, 1));
}

CAMLprim void CVTYPE(get_dky)(value vdata, value vt, value vk, value vy)
{
    CAMLparam4(vdata, vt, vk, vy);

    N_Vector y_nv = NVECTORIZE_VAL(vy);

    int flag = CVodeGetDky(CVODE_MEM_FROM_ML(vdata), Double_val(vt),
			   Int_val(vk), y_nv);
    CHECK_FLAG("CVodeGetDky", flag);
    RELINQUISH_NVECTORIZEDVAL(y_nv);
    
    CAMLreturn0;
}

CAMLprim void CVTYPE(get_err_weights)(value vcvode_mem, value verrws)
{
    CAMLparam2(vcvode_mem, verrws);

    N_Vector errws_nv = NVECTORIZE_VAL(verrws);

    int flag = CVodeGetErrWeights(CVODE_MEM_FROM_ML(vcvode_mem), errws_nv);
    RELINQUISH_NVECTORIZEDVAL(errws_nv);
    CHECK_FLAG("CVodeGetErrWeights", flag);

    CAMLreturn0;
}

CAMLprim void CVTYPE(get_est_local_errors)(value vcvode_mem, value vele)
{
    CAMLparam2(vcvode_mem, vele);

    N_Vector ele_nv = NVECTORIZE_VAL(vele);

    int flag = CVodeGetEstLocalErrors(CVODE_MEM_FROM_ML(vcvode_mem), ele_nv);
    RELINQUISH_NVECTORIZEDVAL(ele_nv);
    CHECK_FLAG("CVodeGetEstLocalErrors", flag);

    CAMLreturn0;
}

