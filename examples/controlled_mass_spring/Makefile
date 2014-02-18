include ../../config

EXAMPLE=controlled_mass_spring.ls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)

controlled_mass_spring.byte: ZLEXTRALIBS += graphics.cma $(OBJ)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.lci *.obc *.ml *.out *.byte *.opt
realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.ls=%.opt) $(EXAMPLE:%.ls=%.byte)

# Common rules
.SUFFIXES : .ml .ls .byte

.ls.ml:
	$(ZLC) $(ZLCFLAGS) -period -s main -sampling 100 $<
	mv main.ml $(<:.ls=)_main.ml

