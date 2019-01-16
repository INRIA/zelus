ZELUC=zeluc
ZLLIB=$(shell $(ZELUC) -where)

OCAMLDEP=ocamldep
OCAMLC=ocamlc
OCAMLOPT=ocamlopt

ML_SRC=misc.ml \
	distribution.ml \
	normalize.ml \
	infer.ml \
	infer_dyn.ml \
	symbolic.ml \
	infer_adf.ml \
	infer_importance.ml

ZLI_SRC=distribution.zli \
	infer.zli \
	symbolic.zli \
	infer_adf.zli \
	infer_importance.zli

OBJ=$(ML_SRC:%.ml=%.cmo)
OBJ_OPT=$(OBJ:%.cmo=%.cmx)
ZCI=$(ZLI_SRC:%.zli=%.zci)

all: byte opt

byte: inference.cma $(ZCI)

opt: inference.cmxa $(ZCI)

inference.cma: $(OBJ)
	$(OCAMLC) -a -o $@ $^

inference.cmxa: $(OBJ_OPT)
	$(OCAMLOPT) -a -o $@ $^

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
	-rm -f inference.cma inference.cmxa inference.a

realclean cleanall: clean
	-rm -f *~
	-rm -f .depend

-include .depend
