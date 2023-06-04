TOOLS=../../tools
OUT_OPTIONS?=-maxt 10 -fullspeed

.PHONY: clutch.out

clutch_graph.pdf: clutch.out clutch.plt
	gnuplot -e "options='$(OUT_OPTIONS)'" clutch.plt > $@

clutch.out: clutch_log_main.exe
	./$< $(OUT_OPTIONS)

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
	-@rm -f *.out
