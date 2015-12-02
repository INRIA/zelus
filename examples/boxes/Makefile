include ../../config

EXAMPLE=boxes.zls
ML=showboxes.ml

all: boxes.byte boxes.opt

boxes.byte: showboxes.cmo boxes.cmo boxes_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) graphics.cma $(ZLEXTRALIBS) $^

boxes.opt: showboxes.cmx boxes.cmx boxes_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) graphics.cmxa \
	    $(ZLEXTRALIBS:.cma=.cmxa) $^

boxes.ml boxes_main.ml: showboxes.zci boxes.zls
	$(ZELUC) $(ZELUCFLAGS) -s main boxes.zls
	mv main.ml boxes_main.ml

# ##

depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

clean:
	-@rm boxes_main.ml boxes.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)
	-@rm -f .depend

realclean cleanall: clean

-include .depend
