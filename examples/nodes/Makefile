all: system.opt

system.ml system_rif.ml: system.zls
	../../bin/zeluc -rif -s system -o system_rif system.zls

system.opt: system.ml system_rif.ml
	ocamlopt -o system.opt unix.cmxa bigarray.cmxa \
			-I `ocamlfind query sundialsml` sundials.cmxa \
			-I ../../lib zllib.cmxa \
			system.ml system_rif.ml

clean:
	-rm -f *.cm[ixo] *.o *.opt *.zci
	-rm -f system.ml
