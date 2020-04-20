OCAMLC=ocamlc
OCAMLOPT=ocamlopt
MENHIR=menhir
MENHIRLIB = /Users/pouzet/.opam/ocaml-base-compiler/lib/menhirLib
OCAMLDEP=ocamldep

BIN = zrun

GENSOURCES = 

DIRECTORIES = .

INCLUDES += $(DIRECTORIES:%=-I %)

OBJ = ident.cmo \
	lident.cmo \
	value.cmo \
	monad.cmo \
	initial.cmo \
	ast.cmo \
	write.cmo \
	coiteration.cmo \
	main.cmo

all: byte opt

opt: $(BIN).opt
byte: $(BIN).byte

$(BIN).opt: $(GENSOURCES) $(OBJ:%.cmo=%.cmx) \
	-I $(MENHIRLIB) menhirLib.cmxa $(OBJ:%.cmo=%.cmx) -o $(BIN).opt

$(BIN).byte: $(GENSOURCES) $(OBJ) main/main.cmo
	$(OCAMLC) $(UNIX) $(OCAMLFLAGS) $(INCLUDES) \
        -I $(MENHIRLIB) menhirLib.cma $(OBJ) -o $(BIN).byte

debug: OCAMLFLAGS += -g
debug: byte 

# Extra dependences
depend: .depend

.depend: $(GENSOURCES)
	$(OCAMLDEP) $(INCLUDES) \
	    $(OBJ:%.cmo=%.mli) $(OBJ:%.cmo=%.ml) \
	    > .depend

ML = $(OBJ:.cmo=.ml)

# implicit rules

.SUFFIXES : .mli .ml .cmi .cmo .cmx .mll .mly .zls .zli .byte .opt

%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $(INCLUDES) $<

%.cmo %.cmi: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c -I $(ZLLIB) $(INCLUDES) $<

%.cmx %.cmi: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -I $(ZLLIB) -c $(INCLUDES:.cma=.cmxa) $<

%.ml: %.mll
	$(OCAMLLEX) $<

%.ml %.mli: %.mly
	$(MENHIR) $(MENHIRFLAGS) $<

wc:
	wc $(ML)

# cleaning:
clean:
	-rm -f .depend
	(for d in $(DIRECTORIES); \
	 do rm -f $$d/*.annot $$d/*.cm[iox] $$d/*.o; \
	 done; \
	 rm -f $(BIN).byte $(BIN).opt *.out \
           $(GENSOURCES) parser.conflicts)

realclean cleanall: clean

-include .depend
