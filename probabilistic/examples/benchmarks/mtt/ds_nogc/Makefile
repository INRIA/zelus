include ../../Makefile.common-config
OWLLIB=../../../../owl
ZELUC=zeluc -copy -I $(INFERLIB) -I $(OWLLIB) -I ../mttlib/


NAME=mtt_ds_nogc
RUN=$(BROOT)/mtt/particles/run.exe
MIN=1
MAX=100
INCR=2
NUMRUNS=10
CSV_FILES=perf.csv perf-step.csv mem.csv mem-ideal.csv accuracy.csv

all: build

test : $(NAME).ml test.ml
	dune build test.exe

publish:
	cp $(CSV_FILES) $(PPL-ZELUS)/data/mtt/particle

bench: bench_per_particles bench_per_steps bench_mem_ideal

include ../../Makefile.common
