ZELUC=zeluc -copy

ZLI=$(wildcard *.zli)
ZCI=$(ZLI:zli=zci)

all: $(ZCI) byte opt

.phony: byte opt

byte:
	dune build probzelus.cma

opt:
	dune build probzelus.cmxa

%.zci: %.zli
	$(ZELUC) -I ../owl $<

clean:
	dune clean
	-rm -f *.zci
cleanall: clean
	rm -f *~


../owl/zelus_owl.zci:
	make -C ../owl

# Dependencies
distribution.zci: ../owl/zelus_owl.zci
infer_ds.zci: distribution.zci ../owl/zelus_owl.zci
infer_ds_gc.zci: distribution.zci  ../owl/zelus_owl.zci
infer_ds_gc_copy.zci: distribution.zci
infer_importance.zci: distribution.zci
infer_pf.zci: distribution.zci
