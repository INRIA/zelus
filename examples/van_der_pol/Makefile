ZELUC=../../compiler/zeluc.byte -I ../../lib

all: byte opt

byte: mainc.byte maind.byte
opt:  mainc.opt maind.opt


mainc.byte: mainc.ml
	ocamlfind ocamlc -o mainc.byte -I `zeluc -where` \
	-package lablgtk2 \
        -package sundialsml lablgtk.cma zllibgtk.cma \
        -linkpkg van_der_pol.ml mainc.ml

mainc.opt: mainc.ml
	ocamlfind ocamlopt -o mainc.opt -I `zeluc -where` \
	-package lablgtk2 \
        lablgtk.cmxa zllibgtk.cmxa \
        -package sundialsml -linkpkg van_der_pol.ml mainc.ml

maind.byte: maind.ml
	ocamlfind ocamlc -o maind.byte -I `zeluc -where` \
	-package lablgtk2 lablgtk.cma unix.cma bigarray.cma zllibgtk.cma \
        -linkpkg van_der_pol.ml maind.ml

maind.opt: maind.ml
	ocamlfind ocamlopt -o maind.opt -I `zeluc -where` \
	-package lablgtk2 lablgtk.cmxa unix.cmxa bigarray.cmxa zllibgtk.cmxa \
        -linkpkg van_der_pol.ml maind.ml

maind.ml: van_der_pol.zls
	$(ZELUC) -gtk2 -s maind -sampling 0.05 van_der_pol.zls

mainc.ml: van_der_pol.zls
	$(ZELUC) -gtk2 -s mainc van_der_pol.zls

clean:
	-@rm -f *.byte
	-@rm -f *.opt
	-@rm -f *.ml *_main.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
