include ../../config

EXAMPLE=stick_slip_friction.zls
ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

stick_slip_friction.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
stick_slip_friction.byte: $(OBJ)

stick_slip_friction.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
stick_slip_friction.opt: $(OBJ:%.cmo=%.cmx)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.zci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.opt) $(EXAMPLE:%.zls=%.byte)

# Common rules
.SUFFIXES : .ml .zls .byte

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -s main -gtk2 $<
	mv main.ml $(<:.zls=)_main.ml

