include ../../config

EXAMPLE=coffee.zls

all: byte
#$(targets)

byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

coffee.byte: coffee.cmo coffee_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma $^

coffee.opt: coffee.cmx coffee_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) graphics.cmxa $^

coffee.byte: INCLUDES += $(GRAPHICS)
coffee.opt: INCLUDES += $(GRAPHICS)

coffee_main.cmo: INCLUDE += $(SUNDIALS)
coffee_main.cmx: INCLUDE += $(SUNDIALS)

coffee.ml coffee_main.ml: coffee.zls
	$(ZELUC) -I $(ZLLIB) $(ZLCFLAGS) -s main -sampling 0 coffee.zls
	mv main.ml coffee_main.ml


depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDE) *.mli *.ml > .depend

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci .depend
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)

realclean cleanall: clean

-include .depend

