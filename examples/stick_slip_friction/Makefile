include ../../config

EXAMPLE=stick_slip_friction.ls
ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

stick_slip_friction.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
stick_slip_friction.byte: $(OBJ)

stick_slip_friction.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
stick_slip_friction.opt: $(OBJ:%.cmo=%.cmx)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.lci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.ls=%.opt) $(EXAMPLE:%.ls=%.byte)

# Common rules
.SUFFIXES : .ml .ls .byte

.ls.ml:
	$(ZLC) $(ZLCFLAGS) -s main -sampling 1 -gtk2 $<
	mv main.ml $(<:.ls=)_main.ml

