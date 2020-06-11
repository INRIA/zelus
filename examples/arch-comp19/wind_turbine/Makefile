include ../../../config

ZELUC = ../../../bin/zeluc
ZLLIB = ../../../lib

OBJ=wt_d.cmx

DEPS=wt_common.zci wt_params.zci

%.ml %.zci: %.zls
	$(ZELUC) $(ZLFLAGS) $<

%.byte: ZLEXTRALIBS=$(ZLGTKLIBS)
%.byte: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			$(INCLUDES) \
	    $< $(<:.ml=_main.ml)
%.opt: ZLEXTRALIBS=$(ZLGTKLIBS)
%.opt: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
			$(INCLUDES) \
	    $< $(<:.ml=_main.ml)

%_main.ml: %.zls
	$(ZELUC) -s main -gtk2 -o $(@:.ml=) $<

# dependencies

default: wt_d.opt

WT_D_DEPS = interp.cmx wt_common.cmx wt_params.cmx

wt_d.opt: INCLUDES += $(WT_D_DEPS)
wt_d.opt: wt_d_main.ml $(WT_D_DEPS)
wt_d.ml: $(WT_D_DEPS:.cmx=.zci)

interp.zci: array.zci
wt_params.zci: array.zci wt_common.zci
wt_params.cmx: wt_common.cmx
wt_common.zci: interp.zci
wt_common.cmx: interp.cmx

#

clean:
	-rm -f wt_d.ml wt_d_main.ml
	-rm -f wt_common.ml wt_params.ml
	-rm -rf *.annot *.zci *.cm[iox] *.o

cleanall realclean: clean
	-rm -rf *.byte *.opt *.out
