include ../../config

EXAMPLE=pendulum.zls

OBJ = data.cmo misc.cmo

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

pendulum.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
pendulum.byte: $(OBJ)

pendulum.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
pendulum.opt: $(OBJ:%.cmo=%.cmx)

pendulum.ml pendulum_main.ml: pendulum.zls
	$(ZELUC) $(ZELUCFLAGS) -s manual -sampling 100 $<
	mv manual.ml pendulum_main.ml

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) main.ml
	-@rm -f $(OBJ:.cmo=.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%_main.ml)

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)

# Common rules
.SUFFIXES : .ml .zls

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) $<

# Dependencies
pendulum.ml: misc.ml data.ml

