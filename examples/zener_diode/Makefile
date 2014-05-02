include ../../config

EXAMPLE=lzc.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

lzc.byte: lzc.cmo lzc_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLGTKLIBS)  $(ZLEXTRALIBS) $^

lzc_main.cmo: lzc_main.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS)  $(ZLEXTRALIBS) -c $^

lzc.ml: lzc.zls
	$(ZELUC) $(ZELUCFLAGS)  -gtk2 -s main -period -sampling 0 lzc.zls
	mv main.ml lzc_main.ml

depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

clean:
	-@rm -f lzc_main.ml
	-@rm -f lzc.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)
	-@rm -f .depend

realclean cleanall: clean

-include .depend
