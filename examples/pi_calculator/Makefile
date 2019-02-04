all: pi_calculator.byte

pi_calculator.byte: pi_calculator.ml main.ml
	ocamlfind ocamlc -o pi_calculator.cli \
									 -I ../../lib -package lablgtk2 -package sundialsml \
									 unix.cma bigarray.cma lablgtk.cma sundials.cma zllibgtk.cma \
									 graphics.cma \
									 pi_calculator.ml cli.ml
	ocamlfind ocamlc -o pi_calculator.plot \
									 -I ../../lib -package lablgtk2 -package sundialsml \
									 unix.cma bigarray.cma lablgtk.cma sundials.cma zllibgtk.cma \
									 graphics.cma \
									 pi_calculator.ml main.ml

pi_calculator.ml main.ml: pi_calculator.zls
	../../bin/zeluc -gtk2 -s main pi_calculator.zls
	../../bin/zeluc -s cli pi_calculator.zls


clean:
	rm -f pi_calculator.ml main.ml cli.ml
	rm -f *.cmi *.cmo *.zci

realclean cleanall: clean
	rm -f pi_calculator.cli pi_calculator.plot
