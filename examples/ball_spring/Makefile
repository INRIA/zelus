include ../../config

EXAMPLE=ball_spring.zls
ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

ball_spring.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
ball_spring.byte: $(OBJ)

ball_spring.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
ball_spring.opt: $(OBJ:%.cmo=%.cmx)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.zci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.opt) $(EXAMPLE:%.zls=%.byte)

# Common rules
.SUFFIXES : .ml .zls .byte

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -s main $<
	mv main.ml $(<:.zls=)_main.ml

