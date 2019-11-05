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
