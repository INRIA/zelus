include ../../config

EXAMPLE=clutch_gui.zls clutch_log.zls
OUT_OPTIONS?=-maxt 10 -fullspeed

.PHONY: clutch.out

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

clutch_graph.pdf: clutch.out clutch.plt
	gnuplot -e "options='$(ZELUCFLAGS); $(OUT_OPTIONS)'" clutch.plt > $@

clutch.out: clutch_log.byte
	./$< $(OUT_OPTIONS)

clutch_gui.byte: ZLEXTRALIBS += $(ZLGTKLIBS) clutch_model.cmo
clutch_gui.byte: clutch_model.cmo

clutch_gui.opt: ZLEXTRALIBS += $(ZLGTKLIBS) clutch_model.cmx
clutch_gui.opt: clutch_model.cmx

clutch_log.byte: ZLEXTRALIBS += clutch_model.cmo
clutch_log.byte: clutch_model.cmo

clutch_log.opt:  ZLEXTRALIBS += clutch_model.cmx
clutch_log.opt: clutch_model.cmx

clutch_diff.byte: ZLEXTRALIBS += clutch_model.cmo
clutch_diff.byte: clutch_model.cmo

clutch_diff.opt:  ZLEXTRALIBS += clutch_model.cmx
clutch_diff.opt: clutch_model.cmx

clutch_model.ml clutch_model.zci: clutch_model.zls
	$(ZELUC) $(ZELUCFLAGS) $<

clutch_gui.ml: clutch_gui.zls clutch_model.zci
	$(ZELUC) $(ZELUCFLAGS) -s main -gtk2 -dzero $<
	mv main.ml $(<:.zls=)_main.ml

clutch_log.ml: clutch_log.zls clutch_model.zci
	$(ZELUC) $(ZELUCFLAGS) -s main $<
	mv main.ml $(<:.zls=)_main.ml

clutch_diff.ml: clutch_diff.zls clutch_model.zci
	$(ZELUC) $(ZELUCFLAGS) -s main $<
	mv main.ml $(<:.zls=)_main.ml

## Compare simulation results with those of Simulink

PLOT_DIFF_OPTS+=--title 'Clutch engagement' --rows 2 --columns 1 --together
# --monochrome

diffs: diff_sundials.pdf

#diffs: diff_sundials.pdf  \
       #diff_sundials-native.pdf \
       #diff_ode45.pdf     \
       #diff_ode23.pdf

sundials.out diff_sundials.pdf: clutch_diff.byte
	./$< -fullspeed -maxt 10
	(head -n 1 clutch.out; \
	 tail -n +2 simulink/ode45.out | head -n 1; \
	 tail -n +2 clutch.out) > sundials.out
	$(TOOLS)/plot_diff $(PLOT_DIFF_OPTS) \
	    sundials.out simulink/ode45.out > diff_sundials.pdf

sundials-native.out diff_sundials-native.pdf: clutch_diff.byte
	./$< -fullspeed -sundials-native-zero-crossings -maxt 10
	(head -n 1 clutch.out; \
	 tail -n +2 simulink/ode45.out | head -n 1; \
	 tail -n +2 clutch.out) > sundials-native.out
	$(TOOLS)/plot_diff $(PLOT_DIFF_OPTS) \
	    sundials-native.out simulink/ode45.out > diff_sundials-native.pdf

ode45.out diff_ode45.pdf: clutch_diff.byte
	./$< -fullspeed -ode45 -maxt 10
	(head -n 1 clutch.out; \
	 tail -n +2 simulink/ode45.out | head -n 1; \
	 tail -n +2 clutch.out) > ode45.out
	$(TOOLS)/plot_diff $(PLOT_DIFF_OPTS) \
	    ode45.out simulink/ode45.out > diff_ode45.pdf

ode23.out diff_ode23.pdf: clutch_diff.byte
	./$< -fullspeed -ode23 -maxt 10
	(head -n 1 clutch.out; \
	 tail -n +2 simulink/ode45.out | head -n 1; \
	 tail -n +2 clutch.out) > ode23.out
	$(TOOLS)/plot_diff $(PLOT_DIFF_OPTS) \
	    ode23.out simulink/ode23.out > diff_ode23.pdf

## Cleaning

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.zci *.obc *.ml *.out *.byte *.opt
	-@rm -f *.out

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.opt) $(EXAMPLE:%.zls=%.byte)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f clutch_model.ml clutch_gui.ml clutch_log.ml
	-@rm -f diff_*.pdf

