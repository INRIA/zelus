include ../../config

EXAMPLE=controlled_mass_spring.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)

controlled_mass_spring.byte: ZLEXTRALIBS += graphics.cma $(OBJ)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.zci *.obc *.ml *.out *.byte *.opt
realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.opt) $(EXAMPLE:%.zls=%.byte)

# Common rules
.SUFFIXES : .ml .zls .byte

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -period -s main -sampling 100 $<
	mv main.ml $(<:.zls=)_main.ml

