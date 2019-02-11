include ../../config

EXAMPLE=test.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

test.byte: test.cmo test_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLGTKLIBS) $^

test.opt: test.cmx test_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLGTKLIBS:.cma=.cmxa) $^

test_main.cmo: test_main.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) -c $^

test_main.cmx: test_main.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) -c $^

test.ml: test.zls
	$(ZELUC) $(ZELUCFLAGS)  -gtk2 -s main -sampling 0 test.zls
	mv main.ml test_main.ml

depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

clean:
	-@rm -f test_main.ml
	-@rm -f test.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)
	-@rm -f .depend

realclean cleanall: clean

-include .depend
