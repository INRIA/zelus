include ../../config

EXAMPLE=controlled_mass_spring.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)

controlled_mass_spring.byte: ZLEXTRALIBS += graphics.cma $(OBJ)

controlled_mass_spring.byte: INCLUDES += $(GRAPHICS)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.zci *.obc *.ml *.out *.byte *.opt
realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.opt) $(EXAMPLE:%.zls=%.byte)

# Common rules
.SUFFIXES : .ml .zls .byte

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -s main $<
	mv main.ml $(<:.zls=)_main.ml

