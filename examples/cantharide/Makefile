include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

VERSIONS=fly.ls \
 	 cantharide1.ls \
         cantharide2.ls \
         cantharide3.ls \
         cantharide4.ls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(VERSIONS:%.ls=%.byte)
opt:  $(VERSIONS:%.ls=%.opt)

fly.ml: ZLCFLAGS+=-gtk2

clean:
	-@rm -f $(VERSIONS:.ls=.ml) $(VERSIONS:.ls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.lci
	-@rm -f $(VERSIONS:%.ls=%.byte) $(VERSIONS:%.ls=%.opt)

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .ls .byte

.ls.ml:
	#$(ZLC) $(ZLCFLAGS) -keepdeadcode -s main -period $<
	$(ZLC) $(ZLCFLAGS) -s main -period $<
	mv main.ml $(<:.ls=)_main.ml

