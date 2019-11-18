INFERLIB=../../../../inference
OWLLIB=../../../../owl
ZELUC=zeluc -copy -I $(INFERLIB) -I $(OWLLIB)


ZLI=$(wildcard *.zli)
ZCI=$(ZLI:zli=zci)

all: $(ZCI) byte opt

.phony: byte opt

byte: metrics.ml
	dune build mttlib.cma

opt: metrics.ml
	dune build mttlib.cmxa

test:
	dune build test.exe

%.zci: %.zli
	$(ZELUC) $<

test.ml : test.zls util.zci
	$(ZELUC) test.zls -s main

metrics.ml : metrics.zls
	$(ZELUC) -noreduce metrics.zls

clean:
	dune clean
	-rm -f *.zci
cleanall: clean
	rm -f *~
