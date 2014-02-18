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

fuelc.ml: fuelc.ls
	$(ZLC) $(ZLCFLAGS) -period -s main -sampling 1 -gtk2 $<
	mv main.ml $(<:.ls=)_main.ml

# TODO: Add dependencies

library.cmo: library.ls mlmisc.lci

fuelc_data.lci: fuelc_data.lsi
fuelc_common.cmo fuelc_common.cmi: fuelc_common.ls lookup.lci fuelc_data.lci
fuelc_engine.cmo fuelc_engine.cmi: fuelc_engine.ls
fuelc_logic.cmo fuelc_logic.cmi:   fuelc_logic.ls
fuelc_subsys.cmo fuelc_subsys.cmi: fuelc_subsys.ls

lookup.cmi: lookup.mli
lookup.cmo: lookup.ml lookup.cmi

mlmisc.cmo mlmisc.cmi: mlmisc.ml lookup.lci

fuelc_data.cmi: fuelc_data.mli
fuelc_data.cmo: fuelc_data.ml fuelc_data.cmi

clean:
	-@rm -f fuelc.ml fuelc_main.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.lci
	-@rm -f fuelc.byte fuelc.opt

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .ls

.ls.ml:
	$(ZLC) $(ZLCFLAGS) $<

