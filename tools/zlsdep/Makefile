include ../../config

BIN = zlsdep
TARGET=opt
OCAMLC= ocamlc

SRC= depend.ml zlsdep.ml

DIRECTORIES = ../../compiler/global ../../compiler/parsing

INCLUDES= -I ../../compiler/global -I ../../compiler/parsing -I $(MENHIRLIB)

OBJ =	../../compiler/global/misc.cmo \
	../../compiler/global/pp_tools.cmo \
	../../compiler/global/ident.cmo \
	../../compiler/parsing/parsetree.cmo \
	../../compiler/global/location.cmo \
	../../compiler/parsing/lexer.cmo \
	../../compiler/parsing/parser.cmo \
	depend.cmo \
	zlsdep.cmo

OBJ_OPT = $(OBJ:.cmo=.cmx) 

INCLUDES = $(DIRECTORIES:%=-I %)

byte: $(BIN).byte
$(BIN).byte: $(OBJ)
	$(OCAMLC) $(OCAMLFLAGS) $(INCLUDES) -I $(MENHIRLIB) menhirLib.cmo $(OBJ) -o $(BIN).byte
	ln -sf $(BIN).byte $(BIN)


all: $(TARGET)
install: install.$(TARGET)
	cp $(BINDIR)/$(BIN).$(TARGET) $(BINDIR)/$(BIN)

uninstall: uninstall.$(TARGET)
	rm -f $(BINDIR)/$(BIN)

# cleaning:
clean:
	rm -f *.cm? *.o *.annot

realclean: clean
	rm -f $(BIN).byte $(BIN).opt $(BIN) *~

cleanall: realclean

# utilities
wc:
	wc -l $(SRC)

include .depend


# implicit rules
.SUFFIXES : .mli .ml .cmi .cmo .cmx .mll

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $(INCLUDES) $<

.ml.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $(INCLUDES) $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $(INCLUDES) $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $(INCLUDES) $<

.mll.ml:
	$(OCAMLLEX) $<

