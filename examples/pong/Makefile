include ../../config

EXAMPLE=pong.zls


default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

pong.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
pong.byte: $(OBJ)

pong.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
pong.opt: $(OBJ:%.cmo=%.cmx)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.zci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.opt) $(EXAMPLE:%.zls=%.byte)

# Common rules
.SUFFIXES : .ml .zls .byte

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -s main -sampling 100 $<
	mv main.ml $(<:.zls=)_main.ml

