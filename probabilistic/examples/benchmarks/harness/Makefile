ZELUC=zeluc
ZLLIB=$(shell $(ZELUC) -where)

OCAMLDEP=ocamldep
OCAMLC=ocamlc -g
OCAMLOPT=ocamlopt

ML_SRC=harness.ml

OBJ=$(ML_SRC:%.ml=%.cmo)
OBJ_OPT=$(OBJ:%.cmo=%.cmx)

all: byte opt

byte: benchlib.cma $(ZCI)

opt: benchlib.cmxa $(ZCI)

benchlib.cma: $(OBJ)
	$(OCAMLC) -a -o $@ $^

benchlib.cmxa: $(OBJ_OPT)
	$(OCAMLOPT) -a -o $@ $^

%.cmo: %.ml
	$(OCAMLC) -I $(ZLLIB) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -I $(ZLLIB) -c $<

depend: .depend

.depend:
	$(OCAMLDEP) $(ML_SRC) \
	    > .depend
# cleaning:
clean:
	-rm -f *.annot *.cm[iox] *.o *.zci
	-rm -f benchlib.cma benchlib.cmxa benchlib.a

realclean cleanall: clean
	-rm -f *~
	-rm -f .depend

-include .depend
