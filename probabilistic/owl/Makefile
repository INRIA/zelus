ZELUC=zeluc -copy
INFERLIB=../inference

ZLI=$(wildcard *.zli)
ZCI=$(ZLI:zli=zci)


all: $(ZCI) byte opt

.phony: byte opt

byte:
	dune build zelus_owl.cma

opt:
	dune build zelus_owl.cmxa

%.zci: %.zli
	$(ZELUC) -I $(INFERLIB) $<

clean:
	dune clean
	-rm -f *.zci
	-rm -f zelus_owl.cma zelus_owl.cmxa
cleanall: clean
	rm -f *~

# Dependencies
mat.zci: owl_types_common.zci

owl_dense_ndarray_generic.zci: owl_types_common.zci

owl_dense_matrix_generic.zci: \
	zelus_owl_types_misc.zci \
	owl_types_common.zci \
	owl_dense_ndarray_generic.zci

owl_dense_matrix_c.zci: \
	zelus_owl_types_misc.zci \
	owl_types_common.zci \
	owl_dense_matrix_generic.zci

owl_dense_matrix_d.zci: \
	zelus_owl_types_misc.zci \
	owl_types_common.zci \
	owl_dense_matrix_generic.zci

owl_dense_matrix_s.zci: \
	zelus_owl_types_misc.zci \
	owl_types_common.zci \
	owl_dense_matrix_generic.zci

owl_dense_matrix_z.zci: \
	zelus_owl_types_misc.zci \
	owl_types_common.zci \
	owl_dense_matrix_generic.zci

linalg_d.zci: \
	zelus_owl_types_misc.zci \
	owl_dense_matrix_d.zci \
	owl_dense_matrix_z.zci \
	owl_dense_matrix_generic.zci

zelus_owl.zci: $(filter-out zelus_owl.zci,$(ZCI))
