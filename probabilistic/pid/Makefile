all: ../ztypes.cmo ../distribution.zci ../infer.zci
	zeluc -I .. -s main pid.zls
	ocamlc -o pid -I ..  -I `zeluc -where` unix.cma  \
               ../distribution.ml ../normalize.ml ../infer.ml \
               pid.ml main.ml

%.zci: %.zli
	zeluc -I .. $<

%.cmo: %.ml
	ocamlc -c $<

clean:
	rm *.zc*
	rm *.cm*
	rm ../*.cm*
	rm ../*.zc*
	rm pid.ml main.ml pid
