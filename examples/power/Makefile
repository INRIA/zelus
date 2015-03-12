include ../../config


APP=
EXAMPLE=$(APP).zls
ML=

ZLEXTRALIBS = $(ZLGTKLIBS)

CMOS=$(ML:%.ml=%.cmo)
CMXS=$(ML:%.ml=%.cmx)
LCIS=$(ML:%.ml=%.zci)

applis=power powerV1
targets=$(applis:%=%.byte)

.SECONDARY: $(applis:%=%.ml)

#default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

run:
	make clean; make; ./$(APP).byte



%.byte: $(CMOS) %.cmo %_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) graphics.cma $(ZLEXTRALIBS) $^

%.opt: $(CMXS) %.cmx %_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) graphics.cmxa \
	    $(ZLEXTRALIBS:.cma=.cmxa) $^

%_main.cmo: INCLUDES += $(SUNDIALS)
%_main.cmx: INCLUDES += $(SUNDIALS)

%.ml %_main.ml: $(LCIS) %.zls
	$(ZELUC) $(ZELUCFLAGS) -s main -dzero -gtk2 $*.zls
	mv main.ml $*_main.ml

depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

clean:
	-@rm -f $(applis:%=%.ml)
	-@rm -f $(applis:%=%_main.ml)
	-@rm -f $(applis:%=%.byte)
	-@rm -f $(applis:%=%.opt)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f .depend

realclean cleanall: clean

-include .depend
