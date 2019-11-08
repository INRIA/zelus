INFERLIB=../../../inference
OWLLIB=../../../owl
ZELUC=zeluc -copy -I $(INFERLIB) -I $(OWLLIB) -I trackerlib

all:
	$(MAKE) -C particles
	$(MAKE) -C ds
	$(MAKE) -C ds_nogc
	$(MAKE) -C ds_bounded

publish:
	$(MAKE) -C particles publish
	$(MAKE) -C ds publish
	$(MAKE) -C ds_nogc publish
	$(MAKE) -C ds_bounded publish

bench:
	$(MAKE) -C particles bench
	$(MAKE) -C ds bench
	$(MAKE) -C ds_nogc bench
	$(MAKE) -C ds_bounded bench

bench_per_particles:
	$(MAKE) -C particles bench_per_particles
	$(MAKE) -C ds bench_per_particles
	echo "Skip:" $(MAKE) -C ds_nogc bench_per_particles
	$(MAKE) -C ds_bounded bench_per_particles

bench_per_steps:
	$(MAKE) -C particles bench_per_steps
	$(MAKE) -C ds bench_per_steps
	$(MAKE) -C ds_nogc bench_per_steps
	$(MAKE) -C ds_bounded bench_per_steps

bench_mem_ideal:
	$(MAKE) -C particles bench_mem_ideal
	$(MAKE) -C ds bench_mem_ideal
	$(MAKE) -C ds_nogc bench_mem_ideal
	$(MAKE) -C ds_bounded bench_mem_ideal

.PHONY: publish bench build

build: trackerlib/lib.zci trackerlib/trackerlib.zci main.ml
	dune build main.exe


%.zci: %.zli
	$(ZELUC) $<


clean:
	-rm -f *.zc*
	$(MAKE) -C trackerlib clean
	$(MAKE) -C particles clean
	$(MAKE) -C ds clean
	$(MAKE) -C ds_nogc clean
	$(MAKE) -C ds_bounded clean

cleanall: clean
	-rm -f *~
	dune clean
	$(MAKE) -C particles cleanall
	$(MAKE) -C ds cleanall
	$(MAKE) -C ds_nogc cleanall
	$(MAKE) -C ds_bounded cleanall
