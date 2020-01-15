include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE=count.zls \
	sincos.zls \
	suspend01.zls \
	ysquared.zls \
	discontinuity.zls \
	hybridaut.zls \
	updown.zls \
	heatingh20.zls \
	khalil.zls \
	sqrt.zls \
	water.zls \
	div_by_zero.zls \
	hardstop_integr.zls \
	derivative.zls \
	zero.zls \
	tabledep.zls \
	input_window.zls \
	euler_forward_error.zls \
	instable.zls \
	ode_non_lipshitz.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

zero.ml: zero.zls unsafe.zci
zero.byte: INCLUDES += unsafe.cmo
zero.byte: unsafe.cmo

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .zls .byte

%.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) -s main -gtk2 $<
	mv main.ml $(<:.zls=)_main.ml

ode_non_lipshitz.byte: ode_non_lipshitz.ml
	ocamlfind ocamlc -o ode_non_lipshitz.byte -I `zeluc -where` \
	-package lablgtk2 \
	-package sundialsml zllibgtk.cma -linkpkg \
	ode_non_lipshitz.ml ode_non_lipshitz_main.ml

ode_non_lipshitz.opt: ode_non_lipshitz.ml
	ocamlfind ocamlopt -o ode_non_lipshitz.opt -I `zeluc -where` \
	-package lablgtk2 \
	-package sundialsml zllibgtk.cmxa -linkpkg \
	ode_non_lipshitz.ml ode_non_lipshitz_main.ml 
