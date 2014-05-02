include ../../config

EXAMPLE=horloge.zls

all: byte
#$(targets)

byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

horloge.byte: draw.cmo horloge.cmo horloge_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma $^

horloge.opt: draw.cmx horloge.cmx horloge_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) graphics.cmxa $^

horloge_main.cmo: INCLUDE += $(SUNDIALS)
horloge_main.cmx: INCLUDE += $(SUNDIALS)

horloge.ml horloge_main.ml: draw.zci horloge.zls
	$(ZELUC) -I $(ZLLIB) $(ZLCFLAGS) -s main -period -sampling 0 horloge.zls
	mv main.ml horloge_main.ml


depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDE) *.mli *.ml > .depend

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci .depend
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)

realclean cleanall: clean

-include .depend

