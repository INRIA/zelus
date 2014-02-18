include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE=suspend01.ls \
	ysquared.ls \
	discontinuity.ls \
	hybridaut.ls \
	updown.ls \
	heatingh20.ls \
	sincos.ls \
	sqrt.ls
#	tabledep.ls


default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

clean:
	-@rm -f $(EXAMPLE:.ls=.ml) $(EXAMPLE:.ls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.lci
	-@rm -f $(EXAMPLE:%.ls=%.byte) $(EXAMPLE:%.ls=%.opt)

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .ls .byte

.ls.ml:
	$(ZLC) $(ZLCFLAGS) -s main -period -sampling 0 -gtk2 $<
	mv main.ml $(<:.ls=)_main.ml

