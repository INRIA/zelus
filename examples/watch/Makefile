include ../../config

EXAMPLE=watch.zls

all: byte
#$(targets)

byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

watch.byte: draw.cmo watch.cmo watch_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma $^

watch.opt: draw.cmx watch.cmx watch_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) graphics.cmxa $^

watch_main.cmo: INCLUDE += $(SUNDIALS)
watch_main.cmx: INCLUDE += $(SUNDIALS)

watch.ml watch_main.ml: draw.zci watch.zls
	$(ZELUC) -I $(ZLLIB) $(ZLCFLAGS) -s main -sampling 0 watch.zls
	mv main.ml watch_main.ml

export:
	mkdir $(DISTDIR)/watch
	cp Makefile draw.ml draw.mli draw.zli readme.md watch.zls \
	   $(DISTDIR)/watch/
	mkdir $(DISTDIR)/watch/img
	cp img/*.png $(DISTDIR)/watch/img/

#

depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDE) *.mli *.ml > .depend

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci .depend
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)

realclean cleanall: clean

-include .depend

