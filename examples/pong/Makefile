include ../../config

EXAMPLE=pong.ls


default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

pong.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
pong.byte: $(OBJ)

pong.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
pong.opt: $(OBJ:%.cmo=%.cmx)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.lci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.ls=%.opt) $(EXAMPLE:%.ls=%.byte)

# Common rules
.SUFFIXES : .ml .ls .byte

.ls.ml:
	$(ZLC) $(ZLCFLAGS) -s main -sampling 100 $<
	mv main.ml $(<:.ls=)_main.ml

