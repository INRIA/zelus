INFERLIB=../../../../../inference
OWLLIB=../../../../../owl
ZELUC=zeluc -copy -I $(INFERLIB) -I $(OWLLIB) -I ..


ZLI=$(wildcard *.zli)
ZCI=$(ZLI:zli=zci)

all: main.ml test.ml
	dune build main.exe

%.zci: %.zli
	$(ZELUC) $<

main.ml test.ml : test.zls 
	$(ZELUC) test.zls -s main

clean:
	dune clean
	-rm -f *.zci
cleanall: clean
	rm -f *~
