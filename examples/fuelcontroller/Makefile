include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

OBJS = lookup.cmo		\
       mlmisc.cmo		\
       library.cmo		\
       fuelc_data.cmo		\
       fuelc_common.cmo		\
       fuelc_engine.cmo		\
       fuelc_subsys.cmo		\
       fuelc_logic.cmo		\
       fuelc.cmo

default: $(word 1, $(targets))
all:  $(targets)
byte: $(OBJS)
opt:  $(OBJS:%.cmo=%.cmx)

fuelc.ml: fuelc.zls
	$(ZELUC) $(ZELUCFLAGS) -period -s main -sampling 1 -gtk2 $<
	mv main.ml $(<:.zls=)_main.ml

# TODO: Add dependencies

library.cmo: library.zls mlmisc.zci

fuelc_data.zci: fuelc_data.zli
fuelc_common.cmo fuelc_common.cmi: fuelc_common.zls lookup.zci fuelc_data.zci
fuelc_engine.cmo fuelc_engine.cmi: fuelc_engine.zls
fuelc_logic.cmo fuelc_logic.cmi:   fuelc_logic.zls
fuelc_subsys.cmo fuelc_subsys.cmi: fuelc_subsys.zls

lookup.cmi: lookup.mli
lookup.cmo: lookup.ml lookup.cmi

mlmisc.cmo mlmisc.cmi: mlmisc.ml lookup.zci

fuelc_data.cmi: fuelc_data.mli
fuelc_data.cmo: fuelc_data.ml fuelc_data.cmi

clean:
	-@rm -f fuelc.ml fuelc_main.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f fuelc.byte fuelc.opt

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .zls

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) $<

