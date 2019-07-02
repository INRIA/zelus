EXAMPLE=heat.zls heatc.zls heatdc.zls
AUX=observers.zls

all: byte opt

byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)


heat.byte: observers.ml heat.ml
	ocamlfind ocamlc -o heat.byte -I `zeluc -where` -package lablgtk2 unix.cma bigarray.cma lablgtk.cma zllibgtk.cma -linkpkg observers.ml heat.ml main.ml

heat.opt: observers.ml heat.ml main.ml
	ocamlfind ocamlopt -o heat.opt -I `zeluc -where` -package lablgtk2 \
        unix.cmxa bigarray.cmxa lablgtk.cmxa zllibgtk.cmxa \
        -linkpkg observers.ml heat.ml main.ml

heatc.byte: heat.ml heatc.ml main.ml
	ocamlfind ocamlc -o heatc.byte -I `zeluc -where` -package lablgtk2 \
        -package sundialsml lablgtk.cma zllibgtk.cma \
        -linkpkg observers.ml heat.ml heatc.ml mainc.ml

heatc.opt: heat.ml heatc.ml main.ml
	ocamlfind ocamlopt -o heatc.opt -I `zeluc -where` -package lablgtk2 \
        lablgtk.cmxa zllibgtk.cmxa \
        -package sundialsml -linkpkg observers.ml heat.ml heatc.ml mainc.ml

heatdc.byte: observers.ml heat.ml heatc.ml heatdc.ml
	ocamlfind ocamlc -o heatdc.byte -I `zeluc -where` -package lablgtk2 \
        -package sundialsml lablgtk.cma zllibgtk.cma \
        -linkpkg observers.ml heat.ml heatc.ml heatdc.ml maindc.ml

heatdc.opt: observers.ml heat.ml heatc.ml heatdc.ml
	ocamlfind ocamlopt -o heatdc.opt -I `zeluc -where` -package lablgtk2 \
        -package sundialsml lablgtk.cmxa zllibgtk.cmxa \
        -linkpkg observers.ml heat.ml heatc.ml heatdc.ml maindc.ml

heat.ml main.ml: heat.zls
	zeluc -sampling 0.1 -gtk2 -s main heat.zls

heatc.ml mainc.ml: heatc.zls
	zeluc -gtk2 -s mainc heatc.zls

#zeluc -sampling 0.1 -gtk2 -s maindc heatdc.zls
heatdc.ml maindc.ml: heatdc.zls
	zeluc -s maindc heatdc.zls

observers.ml: observers.zls
	zeluc observers.zls

clean:
	-@rm -f $(EXAMPLE:%.zls=%.byte)
	-@rm -f $(EXAMPLE:%.zls=%.opt)
	-@rm -f $(opt) $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f $(opt) $(AUX:.zls=.ml) $(AUX:.zls=_main.ml)
	-@rm -f main.ml mainc.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
