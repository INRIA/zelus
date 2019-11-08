EX=coin

all: $(EX)-accuracy.png $(EX)-perf.png $(EX)-perf-step.png $(EX)-mem-ideal.png


$(EX)-accuracy.png: ../$(EX)/particles/accuracy.csv ../$(EX)/ds/accuracy.csv ../$(EX)/ds_bounded/accuracy.csv
	gnuplot -e "ex='$(EX)'" plot-accuracy.gp

$(EX)-perf.png: ../$(EX)/particles/perf.csv ../$(EX)/ds/perf.csv ../$(EX)/ds_bounded/perf.csv
	gnuplot -e "ex='$(EX)'" plot-perf.gp

$(EX)-perf-step.png: ../$(EX)/particles/perf-step.csv ../$(EX)/ds/perf-step.csv ../$(EX)/ds_bounded/perf-step.csv
	gnuplot -e "ex='$(EX)'" plot-perf-step.gp

$(EX)-mem-ideal.png: ../$(EX)/particles/mem-ideal.csv ../$(EX)/ds/mem-ideal.csv ../$(EX)/ds_bounded/mem-ideal.csv
	gnuplot -e "ex='$(EX)'" plot-mem-ideal.gp

clean:

cleanall: clean
	rm -f *.png *~
