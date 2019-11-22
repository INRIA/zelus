INFERLIB=../../../../inference
ZELUC=zeluc -copy -I $(INFERLIB)


ZLI=$(wildcard *.zli)
ZCI=$(ZLI:zli=zci)

all: $(ZCI) byte opt

.phony: byte opt

byte: lib.ml
	dune build slamlib.cma

opt: lib.ml
	dune build slamlib.cmxa


lib.zci lib.ml: lib.zls
	$(ZELUC) $<

%.zci: %.zli
	$(ZELUC) $<

clean:
	dune clean
	-rm -f *.zci lib.ml
cleanall: clean
	rm -f *~
