include ../../config

EXAMPLE=pendulum.ls

OBJ = data.cmo misc.cmo

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

pendulum.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
pendulum.byte: $(OBJ)

pendulum.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
pendulum.opt: $(OBJ:%.cmo=%.cmx)

pendulum.ml pendulum_main.ml: pendulum.ls
	$(ZLC) $(ZLCFLAGS) -s manual -sampling 100 $<
	mv manual.ml pendulum_main.ml

clean:
	-@rm -f $(EXAMPLE:.ls=.ml) main.ml
	-@rm -f $(OBJ:.cmo=.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.lci
	-@rm -f $(EXAMPLE:%.ls=%_main.ml)

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.ls=%.byte) $(EXAMPLE:%.ls=%.opt)

# Common rules
.SUFFIXES : .ml .ls

.ls.ml:
	$(ZLC) $(ZLCFLAGS) $<

# Dependencies
pendulum.ml: misc.ml data.ml

