FILES = updown.zls

TARGET= main

OCAMLC=ocamlc -I `zeluc -where`
OCAMLOPT=ocamlopt -I `zeluc -where`
ZELUC=../../bin/zeluc -I `zeluc -where`

all: byte opt

byte: $(TARGET:%=%.byte)
opt:  $(TARGET:%=%.opt)

main.byte: updown.cmo main.cmo
	ocamlfind ocamlc -o main.byte \
	-I `zeluc -where` \
	-package lablgtk2 unix.cma bigarray.cma \
	lablgtk.cma zllibgtk.cma -linkpkg \
	run.cmo updown.cmo main.cmo

main.opt: updown.cmx main.cmx
	ocamlfind ocamlopt -o main.opt \
	-I `zeluc -where` \
	-package lablgtk2 unix.cmxa bigarray.cmxa \
	lablgtk.cmxa zllibgtk.cmxa -linkpkg \
	run.cmx updown.cmx main.cmx


# dependences

main.ml updown.ml: updown.zls
	$(ZELUC) -s main updown.zls

# implicit rules
.SUFFIXES : .mli .ml .cmi .cmo .cmx .zls .zli *.zci

%.cmi: %.mli
	$(OCAMLC) -c $<

%.cmo %.cmi: %.ml
	$(OCAMLC) -c $<

%.cmx %.cmi: %.ml
	$(OCAMLOPT) -c $<

%.zci: %.zli
	$(ZELUC) $<

%.ml: %.zls
	$(ZELUC) $<

clean:
	-@rm -f $(TARGET:%=%.ml)
	-@rm -f $(TARGET:%=%.byte)
	-@rm -f $(TARGET:%=%.opt)
	-@rm -f $(FILES:.zls=.ml) $(FILES:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci *~

realclean cleanall: clean
