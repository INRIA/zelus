include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE=bangbang.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

export: bangbang.byte
	mkdir $(DISTDIR)/bangbang
	cp bangbang.zls Makefile readme.md $(DISTDIR)/bangbang/
	cp bangbang.byte $(DISTDIR)/bangbang/
	mkdir $(DISTDIR)/bangbang/img
	cp img/*.png $(DISTDIR)/bangbang/img/

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .zls

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -period -s main -sampling 0 -gtk2 $<
	mv main.ml $(<:.zls=)_main.ml

