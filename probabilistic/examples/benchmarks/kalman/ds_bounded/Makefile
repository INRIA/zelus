include ../../Makefile.common-config

NAME=kalman_ds_bounded
RUN=$(BROOT)/kalman/ds_bounded/run.exe
MIN=1
MAX=100
INCR=2
NUMRUNS=10
CSV_FILES=perf.csv perf-step.csv mem.csv mem-ideal.csv accuracy.csv

all: build

publish:
	cp $(CSV_FILES) $(PPL-ZELUS)/data/kalman/ds_bounded

bench: bench_per_particles bench_mem_ideal bench_per_steps

include ../../Makefile.common
