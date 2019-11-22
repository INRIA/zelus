include ../../Makefile.common-config

NAME=gaussian_ds_nogc
RUN=$(BROOT)/gaussian/ds_nogc/run.exe
MIN=100
MAX=1000
P=100
INCR=2
NUMRUNS=10
CSV_FILES=perf.csv perf-step.csv mem.csv mem-ideal.csv accuracy.csv

all: build

publish:
	mkdir -p $(PPL-ZELUS)/data/gaussian/ds_nogc
	cp perf-step.csv mem.csv mem-ideal.csv $(PPL-ZELUS)/data/gaussian/ds_nogc

bench: bench_per_steps bench_mem_ideal

include ../../Makefile.common
