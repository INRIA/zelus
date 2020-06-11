include ../../../config

ZELUC = ../../../bin/zeluc
ZLLIB = ../../../lib

# dependencies

default: cc_d.opt cc_c.opt

cc_d.opt: ZELUCFLAGS += -gtk2 -s main -o cc_d_main
cc_d.opt: ZLEXTRALIBS=$(ZLGTKLIBS)

cc_c.opt: ZELUCFLAGS += -gtk2 -s main -o cc_c_main
cc_c.opt: ZLEXTRALIBS=$(ZLGTKLIBS)

#

clean:
	-rm -f cc_d.ml cc_d_main.ml
	-rm -f cc_c.ml cc_c_main.ml
	-rm -rf *.annot *.zci *.cm[iox] *.o

cleanall realclean: clean
	-rm -rf *.byte *.opt *.out
