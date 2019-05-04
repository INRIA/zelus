ZELUCFLAGS=

all: clean zeluc ocamlc

zeluc: constants.zci draw.zci
	zeluc $(ZELUCFLAGS) noise.zls
	zeluc $(ZELUCFLAGS) vehicle.zls
	zeluc $(ZELUCFLAGS) leader.zls
	zeluc $(ZELUCFLAGS) rear.zls
	zeluc $(ZELUCFLAGS) interior.zls
	zeluc $(ZELUCFLAGS) merging.zls
	zeluc -s main $(ZELUCFLAGS) simu.zls

ocamlc: constants.cmo draw.cmo
	ocamlfind ocamlc -o simu \
		-package zelus.gtk \
		-linkpkg /home/bidet/.opam/4.07.0/lib/ocaml/graphics.cma \
		$^ noise.ml vehicle.ml leader.ml rear.ml interior.ml merging.ml simu.ml main.ml


draw.cmo draw.zli: constants.cmo

%.zli: %.ml
	ocamlc -i $< > $@

%.cmo %.cmi: %.ml
	ocamlc -c $<


%.zci: %.zli
	zeluc $<

clean:
	rm -f simu.ml main.ml vehicle.ml leader.ml rear.ml interior.ml merging.ml noise.ml
	rm -f *.c* *.zci *.zli

mrproper: clean
	rm -f simu
