/***********************************************************************
 *                                                                     *
 *              Ocaml interface to Sundials CVODE solver               *
 *                                                                     *
 *            Timothy Bourke (INRIA) and Marc Pouzet (LIENS)           *
 *                                                                     *
 *  Copyright 2013 Institut National de Recherche en Informatique et   *
 *  en Automatique.  All rights reserved.  This file is distributed    *
 *  under the terms of the GNU Library General Public License, with    *
 *  the special exception on linking described in file LICENSE.        *
 *                                                                     *
 ***********************************************************************/

/* Ocaml interface for custom NVectors. */

#include "nvector_ml.h"

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/unixsupport.h>

#define NVECTOR_OPS_NVCLONE		0
#define NVECTOR_OPS_NVDESTROY		(NVECTOR_OPS_NVCLONE + 1)
#define NVECTOR_OPS_NVSPACE		(NVECTOR_OPS_NVDESTROY + 1)
#define NVECTOR_OPS_NVLINEARSUM		(NVECTOR_OPS_NVSPACE + 1)
#define NVECTOR_OPS_NVCONST		(NVECTOR_OPS_NVLINEARSUM + 1)
#define NVECTOR_OPS_NVPROD		(NVECTOR_OPS_NVCONST + 1)
#define NVECTOR_OPS_NVDIV		(NVECTOR_OPS_NVPROD + 1)
#define NVECTOR_OPS_NVSCALE		(NVECTOR_OPS_NVDIV + 1)
#define NVECTOR_OPS_NVABS		(NVECTOR_OPS_NVSCALE + 1)
#define NVECTOR_OPS_NVINV		(NVECTOR_OPS_NVABS + 1)
#define NVECTOR_OPS_NVADDCONST		(NVECTOR_OPS_NVINV + 1)
#define NVECTOR_OPS_NVMAXNORM		(NVECTOR_OPS_NVADDCONST + 1)
#define NVECTOR_OPS_NVWRMSNORM		(NVECTOR_OPS_NVMAXNORM + 1)
#define NVECTOR_OPS_NVMIN		(NVECTOR_OPS_NVWRMSNORM + 1)

#define NVECTOR_OPS_NVDOTPROD		(NVECTOR_OPS_NVMIN + 1)
#define NVECTOR_OPS_NVCOMPARE		(NVECTOR_OPS_NVDOTPROD + 1)
#define NVECTOR_OPS_NVINVTEST		(NVECTOR_OPS_NVCOMPARE + 1)

#define NVECTOR_OPS_NVWL2NORM		(NVECTOR_OPS_NVINVTEST + 1)
#define NVECTOR_OPS_NVL1NORM		(NVECTOR_OPS_NVWL2NORM + 1)
#define NVECTOR_OPS_NVWRMSNORMMASK	(NVECTOR_OPS_NVL1NORM + 1)
#define NVECTOR_OPS_NVCONSTRMASK	(NVECTOR_OPS_NVWRMSNORMMASK + 1)
#define NVECTOR_OPS_NVMINQUOTIENT	(NVECTOR_OPS_NVCONSTRMASK + 1)

#define NVEC_CONTENT(nvec) ((ml_nvec_content)nvec->content)

#define GET_OP(nvec, x) (Field(NVEC_CONTENT(nvec)->callbacks, x))
#define GET_DATA(nvec) (NVEC_CONTENT(nvec)->data)
#define EMPTY_DATA Val_int(0)

#define HAS_OP(ops, x) (Field(ops, x) != Val_int(0))
#define IS_SOME_OP(nvec, x) (HAS_OP(NVEC_CONTENT(nvec)->callbacks, x))
#define GET_SOME_OP(nvec, x) (Field(Field(NVEC_CONTENT(nvec)->callbacks, x), 0))

static mlsize_t nvec_rough_size =
    sizeof(struct _generic_N_Vector_Ops) + sizeof(struct _ml_nvec_content);

static void nvec_destroy_contents(N_Vector v)
{
    CAMLparam0();
    CAMLlocal1(mlop);

    if (GET_DATA(v) != EMPTY_DATA) {
	if (IS_SOME_OP(v, NVECTOR_OPS_NVDESTROY)) {
	    mlop = GET_SOME_OP(v, NVECTOR_OPS_NVDESTROY);
	    caml_callback(mlop, GET_DATA(v));
	}
	caml_remove_global_root((&NVEC_CONTENT(v)->data));
    }
    caml_remove_generational_global_root((&NVEC_CONTENT(v)->callbacks));

    free(v->ops);
    free(v->content);
    CAMLreturn0;
}

static void finalize_nvec(value nvec)
{
    nvec_destroy_contents(NVEC_VAL(nvec));
}

CAMLprim value ml_nvec_new(value mlops, value data)
{
    CAMLparam2(mlops, data);
    CAMLlocal1(rv);

    N_Vector nv = NULL;
    N_Vector_Ops ops = NULL;
    ml_nvec_content content = NULL;

    /* Create vector */
    rv = caml_alloc_final(sizeof(N_Vector), finalize_nvec,
	    nvec_rough_size, nvec_rough_size * 50);
    nv = NVEC_VAL(rv);

    /* Create vector operation structure */
    ops = (N_Vector_Ops) malloc(sizeof(struct _generic_N_Vector_Ops));
    if (ops == NULL) {
	free(nv);
	caml_failwith("ml_nvec_new: malloc failed for N_Vector_Ops");
    }

    ops->nvclone           = callml_vclone;
    ops->nvcloneempty      = callml_vcloneempty;
    ops->nvdestroy         = callml_vdestroy;

    ops->nvspace = NULL;
    if (HAS_OP(mlops, NVECTOR_OPS_NVSPACE))
	ops->nvspace = callml_vspace;

    ops->nvlinearsum       = callml_vlinearsum;
    ops->nvconst           = callml_vconst;
    ops->nvprod            = callml_vprod;
    ops->nvdiv             = callml_vdiv;
    ops->nvscale           = callml_vscale;
    ops->nvabs             = callml_vabs;
    ops->nvinv             = callml_vinv;
    ops->nvaddconst        = callml_vaddconst;
    ops->nvmaxnorm         = callml_vmaxnorm;
    ops->nvwrmsnorm        = callml_vwrmsnorm;
    ops->nvmin             = callml_vmin;

    ops->nvgetarraypointer = NULL;
    ops->nvsetarraypointer = NULL;

    ops->nvdotprod = NULL;
    if (HAS_OP(mlops, NVECTOR_OPS_NVDOTPROD))
	ops->nvdotprod = callml_vdotprod;

    ops->nvcompare = NULL;
    if (HAS_OP(mlops, NVECTOR_OPS_NVCOMPARE))
	ops->nvcompare = callml_vcompare;

    ops->nvinvtest = NULL;
    if (HAS_OP(mlops, NVECTOR_OPS_NVINVTEST))
	ops->nvinvtest = callml_vinvtest;

    ops->nvwl2norm = NULL;
    if (HAS_OP(mlops, NVECTOR_OPS_NVWL2NORM))
	ops->nvwl2norm = callml_vwl2norm;

    ops->nvl1norm = NULL;
    if (HAS_OP(mlops, NVECTOR_OPS_NVL1NORM))
	ops->nvl1norm = callml_vl1norm;

    ops->nvwrmsnormmask = NULL;
    if (HAS_OP(mlops, NVECTOR_OPS_NVWRMSNORMMASK))
	ops->nvwrmsnormmask = callml_vwrmsnormmask;

    ops->nvconstrmask = NULL;
    if (HAS_OP(mlops, NVECTOR_OPS_NVCONSTRMASK))
	ops->nvconstrmask = callml_vconstrmask;

    ops->nvminquotient = NULL;
    if (HAS_OP(mlops, NVECTOR_OPS_NVMINQUOTIENT))
	ops->nvminquotient = callml_vminquotient;

    /* Create content */
    content = (ml_nvec_content) malloc(sizeof(struct _ml_nvec_content));
    if (content == NULL) {
	free(ops);
	free(nv);
	caml_failwith("ml_nvec_new: malloc failed for ml_vec_content");
    }

    content->callbacks = mlops;
    content->data      = data;
    caml_register_generational_global_root(&content->callbacks);
    caml_register_global_root(&content->data);

    nv->content = content;
    nv->ops     = ops;

    CAMLreturn(rv);
}

CAMLprim value ml_nvec_data(N_Vector v)
{
    CAMLparam0();
    CAMLreturn(GET_DATA(v));
}

CAMLprim N_Vector callml_vcloneempty(N_Vector w)
{
    N_Vector v = NULL;
    N_Vector_Ops ops = NULL;
    ml_nvec_content content = NULL;

    if (w == NULL) return NULL;

    /* Create vector */
    v = (N_Vector) malloc(sizeof *v);
    if (v == NULL) return(NULL);

    /* Create vector operation structure */
    ops = (N_Vector_Ops) malloc(sizeof(struct _generic_N_Vector_Ops));
    if (ops == NULL) { free(v); return(NULL); }

    ops->nvclone           = w->ops->nvclone;
    ops->nvcloneempty      = w->ops->nvcloneempty;
    ops->nvdestroy         = w->ops->nvdestroy;
    ops->nvspace           = w->ops->nvspace;
    ops->nvgetarraypointer = w->ops->nvgetarraypointer;
    ops->nvsetarraypointer = w->ops->nvsetarraypointer;
    ops->nvlinearsum       = w->ops->nvlinearsum;
    ops->nvconst           = w->ops->nvconst;  
    ops->nvprod            = w->ops->nvprod;   
    ops->nvdiv             = w->ops->nvdiv;
    ops->nvscale           = w->ops->nvscale; 
    ops->nvabs             = w->ops->nvabs;
    ops->nvinv             = w->ops->nvinv;
    ops->nvaddconst        = w->ops->nvaddconst;
    ops->nvdotprod         = w->ops->nvdotprod;
    ops->nvmaxnorm         = w->ops->nvmaxnorm;
    ops->nvwrmsnormmask    = w->ops->nvwrmsnormmask;
    ops->nvwrmsnorm        = w->ops->nvwrmsnorm;
    ops->nvmin             = w->ops->nvmin;
    ops->nvwl2norm         = w->ops->nvwl2norm;
    ops->nvl1norm          = w->ops->nvl1norm;
    ops->nvcompare         = w->ops->nvcompare;    
    ops->nvinvtest         = w->ops->nvinvtest;
    ops->nvconstrmask      = w->ops->nvconstrmask;
    ops->nvminquotient     = w->ops->nvminquotient;

    /* Create content */
    content = (ml_nvec_content) malloc(sizeof(struct _ml_nvec_content));
    if (content == NULL) { free(ops); free(v); return(NULL); }

    content->callbacks = NVEC_CONTENT(w)->callbacks;
    content->data = EMPTY_DATA;
    caml_register_generational_global_root(&content->callbacks);
    caml_register_global_root(&content->data);

    /* Attach content and ops */
    v->content = content;
    v->ops     = ops;

    return v;
}

CAMLprim N_Vector callml_vclone(N_Vector w)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    N_Vector v = NULL;

    mlop = GET_OP(w, NVECTOR_OPS_NVCLONE);

    r = caml_callback(mlop, GET_DATA(w));

    v = callml_vcloneempty(w);
    if (v != NULL) {
	NVEC_CONTENT(v)->data = r;
    }

    CAMLreturnT(N_Vector, v);
}

CAMLprim void callml_vdestroy(N_Vector v)
{
    nvec_destroy_contents(v);
    free(v);
}

CAMLprim void callml_vspace(N_Vector v, long int *lrw, long int *liw)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_SOME_OP(v, NVECTOR_OPS_NVSPACE);

    r = caml_callback(mlop, GET_DATA(v));

    *lrw = Long_val(Field(r, 0));
    *liw = Long_val(Field(r, 1));

    CAMLreturn0;
}

CAMLprim void callml_vlinearsum(realtype a, N_Vector x, realtype b, N_Vector y, N_Vector z)
{
    CAMLparam0();
    CAMLlocal1(mlop);
    CAMLlocalN(args, 5);

    mlop = GET_OP(x, NVECTOR_OPS_NVLINEARSUM);

    args[0] = caml_copy_double(a);
    args[1] = NVEC_CONTENT(x)->data;
    args[2] = caml_copy_double(b);
    args[3] = NVEC_CONTENT(y)->data;
    args[4] = NVEC_CONTENT(z)->data;

    caml_callbackN(mlop, 5, args);

    CAMLreturn0;
}

CAMLprim void callml_vconst(realtype c, N_Vector z)
{
    CAMLparam0();
    CAMLlocal1(mlop);
    mlop = GET_OP(z, NVECTOR_OPS_NVCONST);

    caml_callback2(mlop, caml_copy_double(c), NVEC_CONTENT(z)->data);

    CAMLreturn0;
}

CAMLprim void callml_vprod(N_Vector x, N_Vector y, N_Vector z)
{
    CAMLparam0();
    CAMLlocal1(mlop);
    mlop = GET_OP(x, NVECTOR_OPS_NVPROD);

    caml_callback3(mlop, NVEC_CONTENT(x)->data, NVEC_CONTENT(y)->data,
	    NVEC_CONTENT(z)->data);

    CAMLreturn0;
}

CAMLprim void callml_vdiv(N_Vector x, N_Vector y, N_Vector z)
{
    CAMLparam0();
    CAMLlocal1(mlop);
    mlop = GET_OP(x, NVECTOR_OPS_NVDIV);

    caml_callback3(mlop, NVEC_CONTENT(x)->data, NVEC_CONTENT(y)->data,
	    NVEC_CONTENT(z)->data);

    CAMLreturn0;
}

CAMLprim void callml_vscale(realtype c, N_Vector x, N_Vector z)
{
    CAMLparam0();
    CAMLlocal1(mlop);
    mlop = GET_OP(x, NVECTOR_OPS_NVSCALE);

    caml_callback3(mlop, caml_copy_double(c), NVEC_CONTENT(x)->data, 
	    NVEC_CONTENT(z)->data);

    CAMLreturn0;
}

CAMLprim void callml_vabs(N_Vector x, N_Vector z)
{
    CAMLparam0();
    CAMLlocal1(mlop);
    mlop = GET_OP(x, NVECTOR_OPS_NVABS);

    caml_callback2(mlop, NVEC_CONTENT(x)->data, NVEC_CONTENT(z)->data);

    CAMLreturn0;
}

CAMLprim void callml_vinv(N_Vector x, N_Vector z)
{
    CAMLparam0();
    CAMLlocal1(mlop);
    mlop = GET_OP(x, NVECTOR_OPS_NVINV);

    caml_callback2(mlop, NVEC_CONTENT(x)->data, NVEC_CONTENT(z)->data);

    CAMLreturn0;
}

CAMLprim void callml_vaddconst(N_Vector x, realtype b, N_Vector z)
{
    CAMLparam0();
    CAMLlocal1(mlop);
    mlop = GET_OP(x, NVECTOR_OPS_NVADDCONST);

    caml_callback3(mlop, NVEC_CONTENT(x)->data, caml_copy_double(b),
	    NVEC_CONTENT(z)->data);

    CAMLreturn0;
}

CAMLprim realtype callml_vdotprod(N_Vector x, N_Vector y)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_SOME_OP(x, NVECTOR_OPS_NVDOTPROD);

    r = caml_callback2(mlop, NVEC_CONTENT(x)->data, NVEC_CONTENT(y)->data);

    CAMLreturnT(realtype, Double_val(r));
}

CAMLprim realtype callml_vmaxnorm(N_Vector x)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_OP(x, NVECTOR_OPS_NVMAXNORM);

    r = caml_callback(mlop, NVEC_CONTENT(x)->data);

    CAMLreturnT(realtype, Double_val(r));
}

CAMLprim realtype callml_vwrmsnorm(N_Vector x, N_Vector w)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_OP(x, NVECTOR_OPS_NVWRMSNORM);

    r = caml_callback2(mlop, NVEC_CONTENT(x)->data, NVEC_CONTENT(w)->data);

    CAMLreturnT(realtype, Double_val(r));
}

CAMLprim realtype callml_vwrmsnormmask(N_Vector x, N_Vector w, N_Vector id)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_SOME_OP(x, NVECTOR_OPS_NVWRMSNORMMASK);

    r = caml_callback3(mlop, NVEC_CONTENT(x)->data,
	    NVEC_CONTENT(w)->data, NVEC_CONTENT(id)->data);

    CAMLreturnT(realtype, Double_val(r));
}

CAMLprim realtype callml_vmin(N_Vector x)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_OP(x, NVECTOR_OPS_NVMIN);

    r = caml_callback(mlop, NVEC_CONTENT(x)->data);

    CAMLreturnT(realtype, Double_val(r));
}

CAMLprim realtype callml_vwl2norm(N_Vector x, N_Vector w)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_SOME_OP(x, NVECTOR_OPS_NVWL2NORM);

    r = caml_callback2(mlop, NVEC_CONTENT(x)->data, NVEC_CONTENT(w)->data);

    CAMLreturnT(realtype, Double_val(r));
}

CAMLprim realtype callml_vl1norm(N_Vector x)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_SOME_OP(x, NVECTOR_OPS_NVL1NORM);

    r = caml_callback(mlop, NVEC_CONTENT(x)->data);

    CAMLreturnT(realtype, Double_val(r));
}

CAMLprim void callml_vcompare(realtype c, N_Vector x, N_Vector z)
{
    CAMLparam0();
    CAMLlocal1(mlop);
    mlop = GET_SOME_OP(x, NVECTOR_OPS_NVCOMPARE);

    caml_callback3(mlop, caml_copy_double(c),
	    NVEC_CONTENT(x)->data, NVEC_CONTENT(z)->data);

    CAMLreturn0;
}

CAMLprim booleantype callml_vinvtest(N_Vector x, N_Vector z)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_SOME_OP(x, NVECTOR_OPS_NVINVTEST);

    r = caml_callback2(mlop, NVEC_CONTENT(x)->data, NVEC_CONTENT(z)->data);

    CAMLreturnT(booleantype, Bool_val(r));
}

CAMLprim booleantype callml_vconstrmask(N_Vector c, N_Vector x, N_Vector m)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_SOME_OP(x, NVECTOR_OPS_NVCONSTRMASK);

    r = caml_callback3(mlop, NVEC_CONTENT(c)->data,
	    NVEC_CONTENT(x)->data, NVEC_CONTENT(m)->data);

    CAMLreturnT(booleantype, Bool_val(r));
}

CAMLprim realtype callml_vminquotient(N_Vector num, N_Vector denom)
{
    CAMLparam0();
    CAMLlocal2(mlop, r);
    mlop = GET_SOME_OP(num, NVECTOR_OPS_NVMINQUOTIENT);

    r = caml_callback2(mlop, NVEC_CONTENT(num)->data,
	    NVEC_CONTENT(denom)->data);

    CAMLreturnT(realtype, Double_val(r));
}

