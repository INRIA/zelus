include /Users/baudart/Software/zelus-svn/trunk/config

ZELUC = zeluc
EXAMPLE = ltta.zls

all: byte
#$(targets)

byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

ltta.byte: misc.cmo ltta.cmo ltta_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma $^

ltta_main.cmo: INCLUDE += $(SUNDIALS)

ltta.ml ltta_main.ml: misc.zci ltta.zls
	$(ZELUC) -I $(ZLLIB) $(ZLCFLAGS) -s main -sampling 0 ltta.zls
	mv main.ml ltta_main.ml


depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDE) *.mli *.ml > .depend

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci .depend
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)

realclean cleanall: clean

-include .depend

