include ../../../config

ZELUC = ../../../bin/zeluc
ZLLIB = ../../../lib

OBJ=afc_d.cmx afc_c.cmx

DEPS=afc_common.zci afc_utils.zci

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

all: afc_d.opt afc_c.opt

AFC_D_DEPS = afc_interp.cmx afc_delay.cmx afc_utils.cmx

afc_d.opt: INCLUDES += $(AFC_D_DEPS)
afc_d.opt: afc_d_main.ml $(AFC_D_DEPS)
afc_d.ml: $(AFC_D_DEPS:.cmx=.zci)

afc_c.opt: INCLUDES += $(AFC_D_DEPS)
afc_c.opt: afc_c_main.ml $(AFC_D_DEPS)
afc_c.ml: $(AFC_D_DEPS:.cmx=.zci)

afc_interp.zci: array.zci
afc_utils.zci afc_utils.ml: array.zci afc_interp.zci afc_delay.zci
afc_utils.cmx: afc_interp.cmx afc_delay.cmx

#

clean:
	-rm -f afc_d.ml afc_d_main.ml
	-rm -f afc_c.ml afc_c_main.ml
	-rm -f afc_utils.ml
	-rm -rf *.annot *.zci *.cm[iox] *.o

cleanall realclean: clean
	-rm -rf *.byte *.opt *.out
