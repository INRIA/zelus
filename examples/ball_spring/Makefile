include ../../config

EXAMPLE=ball_spring.ls
ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

ball_spring.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
ball_spring.byte: $(OBJ)

ball_spring.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
ball_spring.opt: $(OBJ:%.cmo=%.cmx)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.lci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.ls=%.opt) $(EXAMPLE:%.ls=%.byte)

# Common rules
.SUFFIXES : .ml .ls .byte

.ls.ml:
	$(ZLC) $(ZLCFLAGS) -s main -sampling 100 $<
	mv main.ml $(<:.ls=)_main.ml

