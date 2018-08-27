include ../../config

EXAMPLE=pendulum.zls

OBJ = data.cmo misc.cmo
OCAMLOBJ = aux.cmo

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

pendulum.byte: ZLEXTRALIBS += graphics.cma $(OCAMLOBJ) $(OBJ) 
pendulum.byte: $(OCAMLOBJ) $(OBJ)

pendulum.opt: ZLEXTRALIBS += graphics.cmxa $(OCAMLOBJ) $(OBJ:.cmo=.cmx)
pendulum.opt: $(OCAMLOBJ:%.cmo=%.cmx) $(OBJ:%.cmo=%.cmx)

pendulum.ml pendulum_main.ml: $(OCAMLOBJ:%.cmo=%.zci) $(EXAMPLE)
	$(ZELUC) $(ZELUCFLAGS) -sampling 0.01 -s manual $(EXAMPLE)
	mv manual.ml pendulum_main.ml

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) main.ml
	-@rm -f $(OBJ:.cmo=.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%_main.ml) pendulum.byte

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)

# Common rules
.SUFFIXES : .ml .zls

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) $<

# Dependencies
pendulum.ml: misc.ml data.ml aux.ml

