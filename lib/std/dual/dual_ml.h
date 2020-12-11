/*
 *
 * Dual numbers
 *
 * (c) Benoit Caillaud <benoit.caillaud@inria.fr>, INRIA Rennes, 2013
 *
 */

#ifndef __DUAL_ML_H

#define __DUAL_ML_H

#include <caml/mlvalues.h>

// compare

CAMLprim value dual__compare__ml(value,value);

// make

CAMLprim value dual__make__ml(value,value);

// re

CAMLprim value dual__re__ml(value);

// im

CAMLprim value dual__im__ml(value);

// (+.)

CAMLprim value dual__add__ml(value,value);

// (-.)

CAMLprim value dual__sub__ml(value,value);

// (~-.)

CAMLprim value dual__minus__ml(value);

// ( *. )

CAMLprim value dual__mpy__ml(value,value);

// inv

CAMLprim value dual__inv__ml(value);

// (/.)

CAMLprim value dual__div__ml(value,value);

// sqrt

CAMLprim value dual__sqrt__ml(value);

// exp

CAMLprim value dual__exp__ml(value);

// log

CAMLprim value dual__log__ml(value);

// cos

CAMLprim value dual__cos__ml(value);

// sin

CAMLprim value dual__sin__ml(value);

// tan

CAMLprim value dual__tan__ml(value);

// set_re

CAMLprim value dual__set_re__ml(value,value);

// set_im

CAMLprim value dual__set_im__ml(value,value);

#endif
