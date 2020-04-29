include ../config

GENSOURCES = parser.ml parser.mli lexer.ml

DIRECTORIES=.

OBJ = misc.cmo \
	location.cmo \
	ident.cmo \
	lident.cmo \
	parsetree.cmo \
	parser.cmo \
	lexer.cmo \
	ast.cmo \
	monad.cmo \
	scoping.cmo \
	value.cmo \
	initial.cmo \
	write.cmo \
	coiteration.cmo \
	main.cmo

all: byte opt

opt: $(BIN).opt
byte: $(BIN).byte

$(BIN).opt: $(GENSOURCES) $(OBJ:%.cmo=%.cmx) \
	$(OCAMLOPT) $(UNIXX) $(OCAMLOPTFLAGS) $(INCLUDES) \
	-I $(MENHIRLIB) menhirLib.cmxa $(OBJ:%.cmo=%.cmx) -o $(BIN).opt

$(BIN).byte: $(GENSOURCES) $(OBJ) main/main.cmo
	$(OCAMLC) $(UNIX) $(OCAMLFLAGS) $(INCLUDES) \
        -I $(MENHIRLIB) menhirLib.cma $(OBJ) -o $(BIN).byte

debug: OCAMLFLAGS += -g
debug: byte 

parser.cmo parser.cmi: INCLUDES := -I $(MENHIRLIB) $(INCLUDES)

parser.cmx parser.cmi: INCLUDES := -I $(MENHIRLIB) $(INCLUDES)

# Extra dependences
depend: .depend

.depend: $(GENSOURCES)
	$(OCAMLDEP) $(INCLUDES) \
	    $(OBJ:%.cmo=%.mli) $(OBJ:%.cmo=%.ml) \
	    > .depend

ML = $(OBJ:.cmo=.ml)

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
