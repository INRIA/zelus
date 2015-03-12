include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE= problems2.zls problems.zls doityourself.zls


# billiard1d.zls \
# billiard_ex1.zls billiard_ex2.zls billiard_ex3.zls \
# billiard_ex4.zls billiard_ex4b.zls billiard_ex5.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci *.byte *.ml
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .zls

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -s main -gtk2 $<
	mv main.ml $(^:.zls=)_main.ml

