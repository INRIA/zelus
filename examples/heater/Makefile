FILES = constants.zls io.zls \
	heat.zls heatc.zls heatdc.zls \
	main_heat.zls main_heatc.zls main_heatdc.zls

TARGET= maind mainc maindc 

OCAMLC=ocamlc -I `zeluc -where`
OCAMLOPT=ocamlopt -I `zeluc -where`
ZELUC=zeluc -I `zeluc -where`

all: byte opt

byte: $(TARGET:%=%.byte)
opt:  $(TARGET:%=%.opt)

maind.byte: constants.cmo io.cmo heat.cmo main_heat.cmo maind.cmo
	ocamlfind ocamlc -o maind.byte \
	-I `zeluc -where` \
	-package lablgtk2 unix.cma bigarray.cma \
	lablgtk.cma zllibgtk.cma -linkpkg \
	constants.cmo io.cmo heat.cmo main_heat.cmo maind.cmo

maind.opt: constants.cmx heat.cmx io.cmx main_heat.cmx maind.cmx
	ocamlfind ocamlopt -o maind.opt \
	-I `zeluc -where` \
	-package lablgtk2 unix.cmxa bigarray.cmxa \
	lablgtk.cmxa zllibgtk.cmxa -linkpkg \
	constants.cmx io.cmx heat.cmx main_heat.cmx maind.cmx

mainc.byte: constants.cmo io.cmo heatc.cmo main_heatc.cmo mainc.cmo
	ocamlfind ocamlc -o mainc.byte \
	-I `zeluc -where` \
	-package lablgtk2 \
	-package sundialsml lablgtk.cma zllibgtk.cma -linkpkg \
	constants.cmo io.cmo heat.cmo heatc.cmo main_heatc.cmo mainc.cmo

mainc.opt: constants.cmx io.cmx heatc.cmx main_heatc.cmx mainc.cmx
	ocamlfind ocamlopt -o mainc.opt \
	-I `zeluc -where` \
	-package lablgtk2 \
	-package sundialsml lablgtk.cmxa zllibgtk.cmxa -linkpkg \
	constants.cmx io.cmx heat.cmx heatc.cmx main_heatc.cmx mainc.cmx

maindc.byte: constants.cmo io.cmo heatdc.cmo main_heatdc.cmo maindc.cmo
	ocamlfind ocamlc -o maindc.byte \
	-I `zeluc -where` \
	-package lablgtk2 \
	-package sundialsml lablgtk.cma zllibgtk.cma -linkpkg \
	constants.cmo io.cmo heatc.cmo heatdc.cmo main_heatdc.cmo maindc.cmo

maindc.opt: constants.cmx io.cmx heatdc.cmx main_heatdc.cmx maindc.cmx
	ocamlfind ocamlopt -o maindc.opt \
	-I `zeluc -where` \
	-package lablgtk2 \
	-package sundialsml lablgtk.cmxa zllibgtk.cmxa -linkpkg \
	constants.cmx io.cmx heatc.cmx heatdc.cmx main_heatdc.cmx maindc.cmx

# maindc_no_graphics.byte: constants.cmo io.cmo heatdc.cmo main_heatdc.cmo maindc_nographics.cmo
# 	ocamlfind ocamlc -o maindc.byte \
# 	-I `zeluc -where` \
# 	-package lablgtk2 \
# 	-package sundialsml lablgtk.cma zllibgtk.cma -linkpkg \
# 	constants.cmo io.cmo heatc.cmo heatdc.cmo main_heatdc.cmo maindc.cmo

# maindc_no_graphics.opt: constants.cmx io.cmx heatdc.cmx main_heatdc.cmx maindc_no_graphics.cmx
# 	ocamlfind ocamlopt -o maindc_no_graphics.opt \
# 	-I `zeluc -where` \
# 	-package lablgtk2 \
# 	-package sundialsml lablgtk.cmxa zllibgtk.cmxa -linkpkg \
# 	constants.cmx io.cmx heatc.cmx heatdc.cmx main_heatdc.cmx maindc_no_graphics.cmx

# dependences
heat.ml: constants.ml
heatc.ml: constants.ml
heatdc.ml: constants.ml heatc.ml
main_heat.ml: constants.ml io.ml heat.ml
main_heatc.ml: constants.ml io.ml heat.ml heatc.ml
main_heatdc.ml: constants.ml io.ml heatdc.ml

maind.ml main_heat.ml: main_heat.zls
	$(ZELUC) -gtk2 -s main -sampling 0.1 -o maind main_heat.zls

mainc.ml main_heatc.ml: heatc.ml main_heatc.zls
	$(ZELUC) -gtk2 -s main -o mainc main_heatc.zls

maindc.ml main_heatdc.ml: main_heatdc.zls
	$(ZELUC) -s main -o maindc main_heatdc.zls

# maindc_no_graphics.ml main_heatdc.ml: main_heatdc.zls
# 	$(ZELUC) -gtk2 -s main -o maindc_no_graphics main_heatdc.zls

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
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
