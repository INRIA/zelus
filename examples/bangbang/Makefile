include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE=bangbang.ls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

export: bangbang.byte
	mkdir $(DISTDIR)/bangbang
	cp bangbang.ls Makefile readme.md $(DISTDIR)/bangbang/
	cp bangbang.byte $(DISTDIR)/bangbang/
	mkdir $(DISTDIR)/bangbang/img
	cp img/*.png $(DISTDIR)/bangbang/img/

clean:
	-@rm -f $(EXAMPLE:.ls=.ml) $(EXAMPLE:.ls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.lci
	-@rm -f $(EXAMPLE:%.ls=%.byte) $(EXAMPLE:%.ls=%.opt)

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .ls

.ls.ml:
	$(ZLC) $(ZLCFLAGS) -period -s main -sampling 0 -gtk2 $<
	mv main.ml $(<:.ls=)_main.ml

