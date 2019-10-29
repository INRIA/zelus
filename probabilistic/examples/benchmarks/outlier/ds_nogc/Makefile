include ../../Makefile.common-config

NAME=outlier_ds_nogc
RUN=$(BROOT)/outlier/ds_nogc/run.exe
MIN=100
MAX=100
INCR=2
NUMRUNS=10
CSV_FILES=perf.csv perf-step.csv mem.csv mem-ideal.csv accuracy.csv

all: build

publish:
	cp perf-step.csv mem.csv mem-ideal.csv $(PPL-ZELUS)/data/outlier/ds_nogc

bench: bench_per_steps bench_mem_ideal

include ../../Makefile.common
