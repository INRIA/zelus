INFERLIB=../../../../inference
ZELUC=zeluc -copy -I $(INFERLIB)


ZLI=$(wildcard *.zli)
ZCI=$(ZLI:zli=zci)

all: $(ZCI) byte opt

.phony: byte opt

byte:
	dune build mttlib.cma

opt:
	dune build mttlib.cmxa

%.zci: %.zli
	$(ZELUC) $<

clean:
	dune clean
	-rm -f *.zci
cleanall: clean
	rm -f *~
