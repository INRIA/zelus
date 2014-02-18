/*
 *
 * Dual numbers
 *
 * (c) Benoit Caillaud <benoit.caillaud@inria.fr>, INRIA Rennes, 2013
 *
 */

#include <string.h>
#include <limits.h>
#include <stdio.h>
#include <math.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/fail.h>

#include "dual_ml.h"

// dual number = R x R

typedef struct
{
  double re; // real part
  double im; // imaginary part
} dual;

// Custom block handler

CAMLprim int dual__compare_custom__ml(value,value);

static struct custom_operations dual_block_ops = {
  "fr.inria.zelus.dual.t.1.00", // Version 1.00
  custom_finalize_default,
  dual__compare_custom__ml,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

// compare

CAMLprim int dual__compare_custom__ml(value x,value y)
{
  CAMLparam2(x,y);

  dual * a = (dual *)Data_custom_val(x);
  dual * b = (dual *)Data_custom_val(y);

  /*
   *
   * Warning: there is a difference between IEEE 754 and Dual.t: in Dual.nan is comparable with of dual numbers,
   * while nan is incomparable with all floating point numbers in IEEE 754. The reason is that polymorphic relations
   * (<,>,=,<>,<= and >=) can not be overloaded in OCaml.
   *   
   */

  if (a->re == b->re)
    { CAMLreturn(0); }
  else if (a->re > b->re)
    { CAMLreturn(1); }
  else if (a->re < b->re)
    { CAMLreturn(-1); }
  else
    // special case where atleast one of the members is equal to NaN
    if (isnan(a->re))
      if (isnan(b->re))
	{ CAMLreturn(0); } // both NaN
      else
	{ CAMLreturn(-1); } // only a is NaN
    else
      if (isnan(b->re))
	{ CAMLreturn(1); } // only b is NaN
      else
	{ caml_failwith("Dual.compare: impossible case. Please report bug"); }; // impossible case. Raise exception

}

CAMLprim value dual__compare__ml(value x,value y)
{
  CAMLparam2(x,y);
  CAMLreturn(Val_int(dual__compare_custom__ml(x,y)));
}

// make

CAMLprim value dual__make__ml(value x, value y)
{
  // This function allocates in the heap. We have to use CAMLparam and CAMLlocal.

  CAMLparam2(x,y);
  CAMLlocal1(u); // Custom block

  double p = Double_val(x); // Real part
  double q = Double_val(y); // Imaginary part
  dual * a;; // Vector block within the custom block

  // Custom block allocation
  
  u = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  // Vector block initialization

  a = (dual *)Data_custom_val(u);

  a->re = p;
  a->im = q;

  // Return the custom block

  CAMLreturn(u);
}

// re

CAMLprim value dual__re__ml(value x)
{
  CAMLparam1(x);

  dual * a = (dual *)Data_custom_val(x);

  CAMLreturn(caml_copy_double(a->re));
}

// im

CAMLprim value dual__im__ml(value x)
{
  CAMLparam1(x);

  dual * a = (dual *)Data_custom_val(x);

  CAMLreturn(caml_copy_double(a->im));
}

// (+.)

CAMLprim value dual__add__ml(value x,value y)
{
  CAMLparam2(x,y);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);
  dual * b = (dual *)Data_custom_val(y);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = a->re + b->re;
  c->im = a->im + b->im;

  CAMLreturn(z);
}

// (-.)

CAMLprim value dual__sub__ml(value x,value y)
{
  CAMLparam2(x,y);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);
  dual * b = (dual *)Data_custom_val(y);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = a->re - b->re;
  c->im = a->im - b->im;

  CAMLreturn(z);
}

// (~-.)

CAMLprim value dual__minus__ml(value x)
{
  CAMLparam1(x);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = - a->re;
  c->im = - a->im;

  CAMLreturn(z);
}

// ( *. )

CAMLprim value dual__mpy__ml(value x,value y)
{
  CAMLparam2(x,y);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);
  dual * b = (dual *)Data_custom_val(y);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = a->re * b->re;
  c->im = a->im * b->re + a->re * b->im;

  CAMLreturn(z);
}

// inv

CAMLprim value dual__inv__ml(value x)
{
  CAMLparam1(x);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = 1 / a->re;
  c->im = - a->im / (a->re * a->re);

  CAMLreturn(z);
}

// (/.)

CAMLprim value dual__div__ml(value x,value y)
{
  CAMLparam2(x,y);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);
  dual * b = (dual *)Data_custom_val(y);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = a->re / b->re;
  c->im = a->im / b->re - a->re * b->im / (b->re * b->re);

  CAMLreturn(z);
}

// sqrt

CAMLprim value dual__sqrt__ml(value x)
{
  CAMLparam1(x);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = sqrt(a->re);
  c->im = 0.5 * a->im / c->re;

  CAMLreturn(z);
}

// exp

CAMLprim value dual__exp__ml(value x)
{
  CAMLparam1(x);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = exp(a->re);
  c->im = a->im * c->re;

  CAMLreturn(z);
}

// log

CAMLprim value dual__log__ml(value x)
{
  CAMLparam1(x);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = log(a->re);
  c->im = a->im / c->re;

  CAMLreturn(z);
}

// cos

CAMLprim value dual__cos__ml(value x)
{
  CAMLparam1(x);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = cos(a->re);
  c->im = - a->im * sin(a->re);

  CAMLreturn(z);
}

// sin

CAMLprim value dual__sin__ml(value x)
{
  CAMLparam1(x);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = sin(a->re);
  c->im = a->im * cos(a->re);

  CAMLreturn(z);
}

// tan

CAMLprim value dual__tan__ml(value x)
{
  CAMLparam1(x);
  CAMLlocal1(z);

  dual * a = (dual *)Data_custom_val(x);

  z = caml_alloc_custom(&dual_block_ops,sizeof(dual),0,1);

  dual * c = (dual *)Data_custom_val(z);

  c->re = tan(a->re);
  c->im = a->im * (1 + c->re * c->re);

  CAMLreturn(z);
}

// set_re

CAMLprim value dual__set_re__ml(value x, value y)
{
  CAMLparam2(x,y);

  dual * a = (dual *)Data_custom_val(x);

  a->re = Double_val(y);

  CAMLreturn(Val_unit);
}

// set_im

CAMLprim value dual__set_im__ml(value x, value y)
{
  CAMLparam2(x,y);

  dual * a = (dual *)Data_custom_val(x);

  a->im = Double_val(y);

  CAMLreturn(Val_unit);
}
