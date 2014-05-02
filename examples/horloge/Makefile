all:
	ocamlc -annot  -c  draw.mli	
	ocamlc -annot  -c -I `zeluc -where`  draw.ml
	zeluc -I `zeluc -where` draw.zli
	zeluc -I `zeluc -where` -i -s main -sampling 0 horloge.zls
	ocamlc -annot  -c -I `zeluc -where`  horloge.ml
	ocamlc -annot  -c -I `zeluc -where`  main.ml
	ocamlc -annot  -o horloge.byte  -I `zeluc -where`  bigarray.cma unix.cma zllib.cma graphics.cma draw.cmo horloge.cmo main.cmo

clean:
	rm *~ *.cm* *.zci main.ml horloge.ml *.annot
