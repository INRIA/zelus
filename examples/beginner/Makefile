include ../../config

EXAMPLE=abro.zls button.zls switch.zls hermes.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.zci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.opt) $(EXAMPLE:%.zls=%.byte)

# Common rules
.SUFFIXES : .ml .zls

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -s main $<
	mv main.ml $(<:.zls=)_main.ml

