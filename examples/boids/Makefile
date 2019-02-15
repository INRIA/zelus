#File to compile
FILE=boids

#Zelus compiler
ZELUC=zeluc
SAMPLING=0.1
ZELUCFLAGS=-i

OCAMLC=ocamlc
OCAMLFLAGS=

OCAMLOPT=ocamlopt
OCAMLOPTFLAGS=

EXEC = $(FILE)
EXECOPT = $(FILE).opt

all: opt

byte: $(EXEC)

opt: $(EXECOPT)

$(FILE).ml: $(FILE).zls

$(FILE).cmo: $(FILE).ml
$(FILE): $(FILE).cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $(FILE) unix.cma graphics.cma -I `$(ZELUC) -where` ztypes.cmi $(FILE).cmo

$(FILE).cmx: $(FILE).ml
$(FILE).opt: $(FILE).cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $(FILE).opt unix.cmxa graphics.cmxa -I `$(ZELUC) -where` ztypes.cmx $(FILE).cmx


# implicit rules
.SUFFIXES: .zls .mli .ml .cmi .cmo .cmx .o .zci

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -sampling $(SAMPLING) $<

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c -I `$(ZELUC) -where` $(INCLUDES) $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c -I `$(ZELUC) -where` $(INCLUDES) $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c -I `$(ZELUC) -where` $(INCLUDES) $<

.ml.o:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c -I `$(ZELUC) -where` $(INCLUDES) $<

.mli.zci:
	$(ZELUC) -c $<


clean:
	rm -f *.cm* *.o *.annot *.?annot *.zci \
		$(FILE).ml

realclean: clean
	rm -f $(FILE) $(FILE).opt *~
cleanall: realclean

