include ../../Makefile.common-config
ZELUC+=-I ../slamlib

NAME=slam_ds
RUN=$(BROOT)/slam/ds/run.exe
MIN=1
MAX=1000
P=100
INCR=2
NUMRUNS=10
CSV_FILES=perf.csv perf-step.csv mem.csv mem-ideal.csv accuracy.csv

all: build

publish:
	cp $(CSV_FILES) $(PPL-ZELUS)/data/slam/ds

bench: bench_per_particles bench_per_steps bench_mem_ideal

include ../../Makefile.common
