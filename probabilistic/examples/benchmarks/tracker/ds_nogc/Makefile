include ../../Makefile.common-config
ZELUC+=-I ../trackerlib -I ../../../../owl

NAME=tracker_ds_nogc
RUN=$(BROOT)/tracker/ds_nogc/run.exe
MIN=1
MAX=100
INCR=2
NUMRUNS=10
CSV_FILES=perf.csv perf-step.csv mem.csv mem-ideal.csv accuracy.csv

all: build

publish:
	cp $(CSV_FILES) $(PPL-ZELUS)/data/tracker/ds_nogc

bench: bench_per_particles bench_per_steps bench_mem_ideal

include ../../Makefile.common
