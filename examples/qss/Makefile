EXAMPLE=qss.zls

all: byte opt

byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)


qss.byte: qss.ml main.ml
	ocamlfind ocamlc -o qss.byte -I `zeluc -where` -package lablgtk2 \
        -package sundialsml lablgtk.cma zllibgtk.cma \
        -linkpkg qss.ml main.ml

qss.opt: qss.ml main.ml
	ocamlfind ocamlopt -o qss.opt -I `zeluc -where` -package lablgtk2 \
        lablgtk.cmxa zllibgtk.cmxa \
        -package sundialsml -linkpkg qss.ml main.ml

qss.ml main.ml: qss.zls
	zeluc -gtk2 -s main qss.zls

clean:
	-@rm -f $(EXAMPLE:%.zls=%.byte)
	-@rm -f $(EXAMPLE:%.zls=%.opt)
	-@rm -f $(opt) $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f main.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
