include ../../config

EXAMPLE=suspension.ls
ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

suspension.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
suspension.byte: $(OBJ)

suspension.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
suspension.opt: $(OBJ:%.cmo=%.cmx)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.lci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.ls=%.opt) $(EXAMPLE:%.ls=%.byte)

# Common rules
.SUFFIXES : .ml .ls .byte

.ls.ml:
	$(ZLC) $(ZLCFLAGS) -s main -sampling 1 -gtk2 $<
	mv main.ml $(<:.ls=)_main.ml

