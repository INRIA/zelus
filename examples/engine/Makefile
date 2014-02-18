include ../../config

EXAMPLE=engine.ls
ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

engine.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
engine.byte: $(OBJ)

engine.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
engine.opt: $(OBJ:%.cmo=%.cmx)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.lci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.ls=%.opt) $(EXAMPLE:%.ls=%.byte)

# Common rules
.SUFFIXES : .ml .ls .byte

.ls.ml:
	$(ZLC) $(ZLCFLAGS) -s main -sampling 1 -gtk2 $<
	mv main.ml $(<:.ls=)_main.ml

