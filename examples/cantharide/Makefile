include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

VERSIONS=fly.zls \
 	 cantharide1.zls \
         cantharide2.zls \
         cantharide3.zls \
         cantharide4.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(VERSIONS:%.zls=%.byte)
opt:  $(VERSIONS:%.zls=%.opt)

fly.ml: ZELUCFLAGS+=-gtk2

clean:
	-@rm -f $(VERSIONS:.zls=.ml) $(VERSIONS:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(VERSIONS:%.zls=%.byte) $(VERSIONS:%.zls=%.opt)

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .zls .byte

.zls.ml:
	#$(ZELUC) $(ZELUCFLAGS) -keepdeadcode -s main $<
	$(ZELUC) $(ZELUCFLAGS) -s main $<
	mv main.ml $(<:.zls=)_main.ml

