ZELUC=zeluc -copy
OWLLIB=../owl

ZLI=$(wildcard *.zli)
ZCI=$(ZLI:zli=zci)


all: $(ZCI) byte opt

.phony: byte opt

byte:
	dune build zelus_owl_plplot.cma

opt:
	dune build zelus_owl_plplot.cmxa

%.zci: %.zli
	$(ZELUC) -I $(OWLLIB) $<

clean:
	dune clean
	-rm -f *.zci
	-rm -f zelus_owl_plplot.cma zelus_owl_plplot.cmxa
cleanall: clean
	rm -f *~

../owl/zelus_owl.zci:
	make -C ../owl

# Dependencies
plot.zci: ../owl/zelus_owl.zci
zelus_owl_plplot.zci: $(filter-out zelus_owl_plplot.zci,$(ZCI))
