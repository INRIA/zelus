include ../../config

EXAMPLE=horloge.zls

all: byte
#$(targets)

byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

horloge.byte: draw.cmo horloge.cmo horloge_main.cmo
	$(OCAMLFIND) $(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $^ -package graphics -linkpkg

draw.cmo: draw.ml
	$(OCAMLFIND) $(OCAMLC) $(OCAMLFLAGS) draw.ml -package graphics -linkpkg

draw.cmx: draw.ml
	$(OCAMLFIND) $(OCAMLOPT) $(OCAMLFLAGS) draw.ml -package graphics -linkpkg

horloge.opt: draw.cmx horloge.cmx horloge_main.cmx
	$(OCAMLFIND) $(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
        $^ -package graphics -linkpkg

horloge_main.cmo: INCLUDE += $(SUNDIALS)
horloge_main.cmx: INCLUDE += $(SUNDIALS)

horloge.ml horloge_main.ml: draw.zci horloge.zls
	$(ZELUC) -I $(ZLLIB) $(ZLCFLAGS) -s main -sampling 0 horloge.zls
	mv main.ml horloge_main.ml

export:
	mkdir $(DISTDIR)/horloge
	cp Makefile draw.ml draw.mli draw.zli horloge.zls readme.md \
	   $(DISTDIR)/horloge/
	mkdir $(DISTDIR)/horloge/img
	cp img/*.png $(DISTDIR)/horloge/img/

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

