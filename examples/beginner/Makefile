include ../../config

EXAMPLE=abro.ls button.ls switch.ls hermes.ls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.lci *.obc *.ml *.out *.byte *.opt

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.ls=%.opt) $(EXAMPLE:%.ls=%.byte)

# Common rules
.SUFFIXES : .ml .ls

.ls.ml:
	$(ZLC) $(ZLCFLAGS) -s main -sampling 1 $<
	mv main.ml $(<:.ls=)_main.ml

