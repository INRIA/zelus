include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE= problems2.ls problems.ls doityourself.ls


# billiard1d.ls \
# billiard_ex1.ls billiard_ex2.ls billiard_ex3.ls \
# billiard_ex4.ls billiard_ex4b.ls billiard_ex5.ls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

clean:
	-@rm -f $(EXAMPLE:.ls=.ml) $(EXAMPLE:.ls=_main.ml)
	-@rm -f $(EXAMPLE:.ls=.ml) $(EXAMPLE:.ls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.lci *.byte *.ml
	-@rm -f $(EXAMPLE:%.ls=%.byte) $(EXAMPLE:%.ls=%.opt)

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .ls

.ls.ml:
	$(ZLC) $(ZLCFLAGS) -s main -sampling 10 -gtk2 -period $<
	mv main.ml $(^:.ls=)_main.ml

