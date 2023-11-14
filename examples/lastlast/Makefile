include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE=lastlast.zls
OCAMLFLAGS += -w -26

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

export: lastlast.byte
	mkdir $(DISTDIR)/lastlast
	cp lastlast.zls Makefile readme.md $(DISTDIR)/lastlast/
	cp lastlast.byte $(DISTDIR)/lastlast/
	mkdir $(DISTDIR)/lastlast/img
	cp img/*.png $(DISTDIR)/lastlast/img/

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .zls

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -s main -gtk2 $<
	mv main.ml $(<:.zls=)_main.ml

