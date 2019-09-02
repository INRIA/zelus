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
	-package lablgtk2 \
	lablgtk.cma zllibgtk.cma \
        -package sundialsml -linkpkg van_der_pol.ml maind.ml

maind.opt: maind.ml
	ocamlfind ocamlopt -o maind.opt -I `zeluc -where` \
	-package lablgtk2 \
	lablgtk.cmxa zllibgtk.cmxa \
        -package sundialsml -linkpkg van_der_pol.ml maind.ml

maincgraphics.byte: maincgraphics.ml
	ocamlfind ocamlc -o maincgraphics.byte -I `zeluc -where` \
	-package lablgtk2 \
        -package sundialsml lablgtk.cma zllibgtk.cma \
        -linkpkg van_der_pol.ml maincgraphics.ml

maincgraphics.opt: maincgraphics.ml
	ocamlfind ocamlopt -o maincgraphics.opt -I `zeluc -where` \
	-package lablgtk2 \
        lablgtk.cmxa zllibgtk.cmxa \
        -package sundialsml -linkpkg van_der_pol.ml maincgraphics.ml

maindgraphics.byte: maindgraphics.ml
	ocamlfind ocamlc -o maindgraphics.byte -I `zeluc -where` \
	-package lablgtk2 \
	lablgtk.cma zllibgtk.cma \
        -package sundialsml -linkpkg van_der_pol.ml maindgraphics.ml

maindgraphics.opt: maindgraphics.ml
	ocamlfind ocamlopt -o maindgraphics.opt -I `zeluc -where` \
	-package lablgtk2 \
	lablgtk.cmxa zllibgtk.cmxa \
        -package sundialsml -linkpkg van_der_pol.ml maindgraphics.ml

maind.ml: van_der_pol.zls
	$(ZELUC) -s maind van_der_pol.zls

mainc.ml: van_der_pol.zls
	$(ZELUC) -s mainc van_der_pol.zls

maindgraphics.ml: van_der_pol.zls
	$(ZELUC) -gtk2 -s maindgraphics -sampling 0.05 van_der_pol.zls

maincgraphics.ml: van_der_pol.zls
	$(ZELUC) -gtk2 -s maincgraphics van_der_pol.zls

clean:
	-@rm -f *.byte
	-@rm -f *.opt
	-@rm -f *.ml *_main.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci *~

realclean cleanall: clean
