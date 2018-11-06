EXAMPLE=heat.zls smartheat.zls smartheat2.zls

all: byte

byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)


heat.byte: heat.ml
	ocamlfind ocamlc -o heat.byte -I `zeluc -where` -package lablgtk2 unix.cma bigarray.cma lablgtk.cma zllibgtk.cma -linkpkg heat.ml main.ml

heat.opt: heat.ml main.ml
	ocamlfind ocamlopt -o heat.opt -I `zeluc -where` -package lablgtk2 \
        unix.cmxa bigarray.cmxa lablgtk.cmxa zllibgtk.cmxa \
        -linkpkg heat.ml main.ml

heatc.byte: heat.ml heatc.ml main.ml
	ocamlfind ocamlc -o heatc.byte -I `zeluc -where` -package lablgtk2 \
        unix.cma bigarray.cma lablgtk.cma zllibgtk.cma -package sundialsml \
        -linkpkg heat.ml heatc.ml mainc.ml

heatc.opt: heat.ml heatc.ml main.ml
	ocamlfind ocamlopt -o heatc.opt -I `zeluc -where` -package lablgtk2 \
        lablgtk.cmxa zllibgtk.cmxa -package sundialsml \
        -linkpkg heat.ml heatc.ml mainc.ml

smartheat.byte: smartheat.ml
	ocamlfind ocamlc -o smartheat.byte -I `zeluc -where` \
        -I .. \
        -package lablgtk2 \
        unix.cma bigarray.cma lablgtk.cma zllibgtk.cma -linkpkg \
        ../distribution.ml \
        ../normalize.ml \
        ../infer.ml \
        heat.ml smartheat.ml mains.ml

smartheat.opt: smartheat.ml
	ocamlfind ocamlopt -o smartheat.opt -I `zeluc -where` \
        -I .. \
        -package lablgtk2 \
        unix.cmxa bigarray.cmxa lablgtk.cmxa zllibgtk.cmxa -linkpkg \
        ../distribution.ml \
        ../normalize.ml \
        ../infer.ml \
        heat.ml smartheat.ml mains.ml

smartheat.ml mains: smartheat.zls
	zeluc -I .. -s mains smartheat.zls

smartheat2.byte: smartheat2.ml ../infer.ml
	ocamlfind ocamlc -o smartheat2.byte -I `zeluc -where` \
	-I .. \
        -package lablgtk2 \
        unix.cma bigarray.cma lablgtk.cma zllibgtk.cma -linkpkg \
        ../distribution.ml \
        ../normalize.ml \
        ../infer.ml \
        heat.ml smartheat2.ml mains2.ml

smartheat2.ml mains2: smartheat2.zls
	zeluc -noreduce -I .. -sampling 0.1 -s mains2 smartheat2.zls

heat.ml main.ml: heat.zls
	zeluc -i -I `zeluc -where` -sampling 0.1 -gtk2 -s main heat.zls

heatc.ml mainc.ml: heatc.zls
	zeluc -gtk2 -s mainc heatc.zls

clean:
	-@rm -f $(EXAMPLE:%.zls=%.byte)
	-@rm -f $(EXAMPLE:%.zls=%.opt)
	-@rm -f $(opt) $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f main.ml mainc.ml mains.ml mains2.ml

realclean cleanall: clean
