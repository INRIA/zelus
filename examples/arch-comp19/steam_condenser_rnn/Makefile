include ../../../config

ZELUC = ../../../bin/zeluc
ZLLIB = ../../../lib

OBJ=sc_d.cmx

DEPS=sc_utils.zci

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

default: sc_d.opt

SC_D_DEPS = sc_interp.cmx sc_utils.cmx

sc_d.opt: INCLUDES += $(SC_D_DEPS)
sc_d.opt: sc_d_main.ml $(SC_D_DEPS)
sc_d.ml: $(SC_D_DEPS:.cmx=.zci)

sc_interp.zci: array.zci
sc_utils.zci: array.zci

#

clean:
	-rm -f sc_d.ml sc_d_main.ml
	-rm -f sc_utils.ml
	-rm -rf *.annot *.zci *.cm[iox] *.o

cleanall realclean: clean
	-rm -rf *.byte *.opt *.out
