ZELUC=zeluc
ZLLIB=`$(ZELUC) -where`

OCAMLDEP=ocamldep
OCAMLC=ocamlc
OCAMLOPT=ocamlopt

ML_SRC=gridworld.ml
ZLI_SRC=gridworld.zli

OBJ=$(ML_SRC:%.ml=%.cmo)
OBJ_OPT=$(OBJ:%.cmo=%.cmx)
ZCI=$(ZLI_SRC:%.zli=%.zci)

all: byte opt

byte: $(OBJ) $(ZCI)

opt: $(OBJ_OPT) $(ZCI)


%.cmo: %.ml
	$(OCAMLC) -I $(ZLLIB) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -I $(ZLLIB) -c $<

%.zci: %.zli
	$(ZELUC) $<

depend: .depend

.depend:
	$(OCAMLDEP) $(ML_SRC) \
	    > .depend
# cleaning:
clean:
	-rm -f *.annot *.cm[iox] *.o *.zci

realclean cleanall: clean
	-rm -f *~
	-rm -f .depend

-include .depend
