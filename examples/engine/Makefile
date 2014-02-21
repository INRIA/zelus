include ../../config

EXAMPLE=engine.zls
ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

engine.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
engine.byte: $(OBJ)

engine.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
engine.opt: $(OBJ:%.cmo=%.cmx)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.zci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.opt) $(EXAMPLE:%.zls=%.byte)

# Common rules
.SUFFIXES : .ml .zls .byte

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -s main -sampling 1 -gtk2 $<
	mv main.ml $(<:.zls=)_main.ml

