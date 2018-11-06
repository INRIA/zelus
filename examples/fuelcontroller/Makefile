include ../../config

PLOT_DIFF = ../../tools/plot_diff
ZLEXTRALIBS = $(ZLGTKLIBS)

OBJS = lookup.cmo		\
       mlmisc.cmo		\
       library.cmo		\
			 fuelc_data.cmo		\
			 fuelc_common.cmo		\
			 fuelc_logic.cmo		\
       fuelc_engine.cmo		\
       fuelc_subsys.cmo

EXECUTABLES = fuelc_testengineonly.byte \
				      fuelc_testcontrolleronly.byte \
				      fuelc_basicfuel.byte \
				      fuelc_mapfail.byte

TARGET     = fuelc_basicfuel.byte \
				     fuelc_mapfail.byte
DUMPTARGET = dumpnode_basicfuel.byte \
				 		 dumpnode_mapfail.byte
PLOTTARGET = diff_basicfuel.pdf \
				 		 diff_mapfail.pdf

default: $(word 1, $(targets))
all:  $(targets) dumpall diff_plot
byte: $(OBJS) $(TARGET)
opt:  $(OBJS:%.cmo=%.cmx) $(TARGET:.byte=.opt)

dump: dumpbyte
dumpall: $(targets:%=dump%)
dumpbyte: $(OBJS) $(DUMPTARGET)
dumpopt: $(OBJS:.cmo=.cmx) $(DUMPTARGET:.byte=.opt)

diff_plot: $(PLOTTARGET)
diff_%.pdf: diff_plots/zls_%.out diff_plots/slk_%.out
	$(PLOT_DIFF) -c 1 -r 2 --together $^ > diff_plots/$@

%.byte: INCLUDES += $(OBJS)
%.opt : INCLUDES += $(OBJS:.cmo=.cmx)

$(EXECUTABLES:.byte=.ml): fuelc.zls library.zci fuelc_engine.zci fuelc_subsys.zci
	$(ZELUC) $(ZELUCFLAGS) -s $(@:fuelc_%.ml=%) $<
	mv $(@:fuelc_%=%) $@

fuelc.ml: fuelc.zls fuelc_engine.zci fuelc_subsys.zci library.zci
	$(ZELUC) $(ZELUCFLAGS) $<

fuelc_%.byte: ZELUCFLAGS += -gtk2
fuelc_%.byte: fuelc.ml fuelc_%.ml library.cmo fuelc_engine.cmo fuelc_subsys.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
	    $(INCLUDES) $< $(@:.byte=.ml)

fuelc_%.opt: ZELUCFLAGS += -gtk2
fuelc_%.opt: fuelc.ml fuelc_%.ml library.cmx fuelc_engine.cmx fuelc_subsys.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
      $(INCLUDES) $< $(@:.opt=.ml)

$(DUMPTARGET:.byte=.ml): \
						dumpnode.zls fuelc.zci fuelc_engine.zci fuelc_subsys.zci library.zci
	$(ZELUC) $(ZELUCFLAGS) -s $(@:dumpnode_%.ml=%) $<
	mv $(@:dumpnode_%=%) $@

dumpnode.ml: dumpnode.zls fuelc.zci fuelc_engine.zci fuelc_subsys.zci library.zci
	$(ZELUC) $(ZELUCFLAGS) $<

dumpnode_%.byte: INCLUDES += fuelc.ml
dumpnode_%.byte: dumpnode.ml dumpnode_%.ml fuelc.ml \
								 library.cmo fuelc_engine.cmo fuelc_subsys.cmo
	echo $@ $<
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
	    $(INCLUDES) $< $(@:.byte=.ml)

dumpnode_%.opt: INCLUDES += fuelc.ml
dumpnode_%.opt: dumpnode.ml dumpnode_%.ml fuelc.ml \
								library.cmx fuelc_engine.cmx fuelc_subsys.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
    	-I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
    	$(INCLUDES) $< $(@:.opt=.ml)

# TODO: Add dependencies

library.cmo library.cmx: library.zls mlmisc.zci mlmisc.cmo

fuelc_common.cmo fuelc_common.cmx fuelc_common.cmi: fuelc_common.zls \
																										lookup.zci \
																										fuelc_data.zci
fuelc_engine.cmo fuelc_engine.cmx fuelc_engine.cmi: fuelc_engine.zls
fuelc_logic.cmo fuelc_logic.cmx fuelc_logic.cmi   : fuelc_logic.zls \
																										fuelc_data.cmo \
																										fuelc_common.cmo
fuelc_subsys.cmo fuelc_subsys.cmx fuelc_subsys.cmi: fuelc_subsys.zls \
																										fuelc_common.zci \
																										fuelc_logic.zci \
																										fuelc_logic.cmo

lookup.cmo lookup.cmx: lookup.ml lookup.cmi
mlmisc.cmo mlmisc.cmx: mlmisc.ml lookup.zci lookup.cmo
fuelc_data.cmo fuelc_data.cmx: fuelc_data.ml fuelc_data.cmi

fuelc_subsys.ml: fuelc_logic.zci fuelc_common.zci library.zci

clean:
	-@rm -f fuelc.ml fuelc_main.ml
	-@rm -f dumpnode.ml dumpnode_main.ml
	-@rm -f fuelc_common.ml fuelc_engine.ml fuelc_logic.ml fuelc_subsys.ml
	-@rm -f library.ml
	-@rm -f $(EXECUTABLES:.byte=.ml)
	-@rm -f $(DUMPTARGET:.byte=.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
	-@rm -f *.out
	-@rm -f $(DUMPTARGET) $(DUMPTARGET:.byte=.opt)
	-@rm -f $(EXECUTABLES) $(EXECUTABLES:.byte=.opt) 
	-@rm -f $(PLOTTARGET:%=diff_plots/%)

# Common rules
.SUFFIXES : .ml .zls

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) $<
