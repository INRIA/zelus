include ../../../config

ZELUC = ../../../bin/zeluc
ZLLIB = ../../../lib

OBJ=nn_d.cmx

DEPS=nn_utils.zci

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

all: nn_d.opt

NN_D_DEPS = nn_utils.cmx

nn_d.opt: INCLUDES += $(NN_D_DEPS)
nn_d.opt: nn_d_main.ml $(NN_D_DEPS)
nn_d.ml: $(NN_D_DEPS:.cmx=.zci)

nn_c.opt: INCLUDES += $(NN_D_DEPS)
nn_c.opt: nn_c_main.ml $(NN_D_DEPS)
nn_c.ml: $(NN_D_DEPS:.cmx=.zci)

#

clean:
	-rm -f nn_d.ml nn_d_main.ml
	-rm -f nn_utils.ml
	-rm -rf *.annot *.zci *.cm[iox] *.o

cleanall realclean: clean
	-rm -rf *.byte *.opt *.out
