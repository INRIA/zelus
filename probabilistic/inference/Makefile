ZELUC=zeluc
ZLLIB=$(shell $(ZELUC) -where)

OCAMLDEP=ocamldep
OCAMLC=ocamlc -g
OCAMLOPT=ocamlopt

ML_SRC=misc_lib.ml \
	distribution.ml \
	normalize.ml \
	infer.ml \
	infer_dyn.ml \
	symbolic.ml \
	infer_adf.ml \
	infer_importance.ml \
	infer_ds_ll.ml \
	infer_ds.ml
	infer_ds_ll_gc.ml \
	distribution_ds.ml
>>>>>>> delayed-sampling-gc

ZLI_SRC=distribution.zli \
	infer.zli \
	symbolic.zli \
	infer_adf.zli \
	infer_importance.zli \
	infer_ds_ll.zli \
	infer_ds.zli
	infer_ds_ll_gc.zli \
	distribution_ds.zli

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
