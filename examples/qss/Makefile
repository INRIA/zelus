EXAMPLE=qss1.zls qss2.zls

all: byte opt

byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)


qss1.byte: qss1.ml main.ml
	ocamlfind ocamlc -o qss1.byte -I `zeluc -where` -package lablgtk2 \
        -package sundialsml lablgtk.cma zllibgtk.cma \
        -linkpkg qss1.ml main.ml

qss1.opt: qss1.ml main.ml
	ocamlfind ocamlopt -o qss1.opt -I `zeluc -where` -package lablgtk2 \
        lablgtk.cmxa zllibgtk.cmxa \
        -package sundialsml -linkpkg qss1.ml main.ml

qss1.ml: qss1.zls
	zeluc -gtk2 -s main qss1.zls

qss2.byte: qss2.ml main.ml
	ocamlfind ocamlc -o qss2.byte -I `zeluc -where` -package lablgtk2 \
        -package sundialsml lablgtk.cma zllibgtk.cma \
        -linkpkg qss2.ml main.ml

qss2.opt: qss2.ml main.ml
	ocamlfind ocamlopt -o qss2.opt -I `zeluc -where` -package lablgtk2 \
        lablgtk.cmxa zllibgtk.cmxa \
        -package sundialsml -linkpkg qss2.ml main.ml

qss2.ml: qss2.zls
	zeluc -gtk2 -s main qss2.zls

clean:
	-@rm -f $(EXAMPLE:%.zls=%.byte)
	-@rm -f $(EXAMPLE:%.zls=%.opt)
	-@rm -f $(opt) $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f main.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
