ZELUC=zeluc
OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep

SUNDIALS=-I /home/virgile/.opam/4.02.1/lib/sundialsml
SUNDIALS_CVODE = sundials.cma

ZLLIBS = /home/virgile/.local/src/zelus-1.0.0-sundials-byte/lib
ZLSTDLIBS = bigarray.cma unix.cma $(SUNDIALS) $(SUNDIALS_CVODE)
ZLEXTRALIBS = zllib.cma
#ZLGTKLIBS = $(LABLGTK2) lablgtk.cma zllibgtk.cma

INCLUDES = $(ZLLIBS) $(ZLSTDLIBS) graphics.cma $(ZLEXTRALIBS)

stick_slip.byte: util.cmo stick_slip.cmo main.cmo
	$(OCAMLC) -o $@ -I $(INCLUDES) $^

stick_slip.opt: util.cmx stick_slip.cmx main.cmx
	$(OCAMLOPT) -o $@ -I $(INCLUDES:.cma=.cmxa) $^

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx .zls .zli .zci
.PHONY: clean depend

.ml.cmo:
	$(OCAMLC) -I $(INCLUDES) -c $<

.ml.cmx:
	$(OCAMLOPT) -I $(INCLUDES:.cma=.cmxa) -c $<

.zli.zci:
	$(ZELUC) $<

stick_slip.ml main.ml: util.zci stick_slip.zls
	$(ZELUC) -s main stick_slip.zls

clean:
	rm -f stick_slip.byte stick_slip.opt
	rm -f stick_slip.ml main.ml util.byte util.opt
	rm -f *.cm[iox]
	rm -f *.zci
	rm -f *.o

depend: *.mli *.ml
	$(OCAMLDEP) $(INCLUDES) $^ > .depend

include .depend

