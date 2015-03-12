include ../../config

ZELUC = ../../compiler/zeluc.byte
ZLLIB =  ../../lib/
ZELUCFLAGS = -I $(ZLLIB)

EXAMPLE=timing_test.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

timing_test.byte: misc.cmo timing_test.cmo timing_test_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLGTKLIBS) $^

timing_test_main.cmo: misc.cmo timing_test_main.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) -c $^

timing_test.ml: misc.zci timing_test.zls
	$(ZELUC) $(ZELUCFLAGS) -I $(ZLLIB) -s main -sampling 0 timing_test.zls
	mv main.ml timing_test_main.ml

depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

clean:
	-@rm -f timing_test_main.ml
	-@rm -f timing_test.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)
	-@rm -f .depend

realclean cleanall: clean

-include .depend
