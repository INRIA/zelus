all: ../ztypes.cmo ../distribution.zci ../infer.zci display.zci
	zeluc -I .. -s main hmm.zls
	ocamlc -o hmm -I .. unix.cma graphics.cma \
               ../distribution.ml ../normalize.ml ../infer.ml display.ml \
               hmm.ml main.ml

%.zci: %.zli
	zeluc -I .. $<

%.cmo: %.ml
	ocamlc -c $<

clean:
	rm -f *.zc*
	rm -f *.cm*
	rm -f ../*.cm*
	rm -f ../*.zc*
	rm -f hmm.ml main.ml

cleanall: clean
	rm -f hmm
