PPL-ZELUS=$(HOME)/probabilistic/mit-ibm/ppl-zelus
ZELUC=zeluc -copy
ZLLIB=$(shell $(ZELUC) -where)
INFERLIB=../../../../inference
BENCHLIB=../../harness

INFERENCE_CMA=$(INFERLIB)/inference.cma
INFERENCE_CMXA=$(INFERLIB)/inference.cmxa
INFERENCE_ZCI=$(INFERLIB)/distribution.zci $(INFERLIB)/infer.zci

BENCHLIB_CMA=$(BENCHLIB)/benchlib.cma
BENCHLIB_CMXA=$(BENCHLIB)/benchlib.cmxa


OCAMLDEP=ocamldep
OCAMLC=ocamlc -g
OCAMLOPT=ocamlopt

NAME=slam_particles
MIN=1
MAX=100
INCR=2
NUMRUNS=10
WARMUP=1

CSV_FILES=perf.csv perf-step.csv mem.csv mem-ideal.csv accuracy.csv

all: opt

.PHONY: $(INFERENCE_CMA) $(INFERENCE_CMXA) $(BENCHLIB_CMA) $(BENCHLIB_CMXA) \
	bench_per_particles bench_per_steps bench_mem_ideal bench publish

byte: $(NAME)
opt: $(NAME).opt

publish:
	cp $(CSV_FILES) $(PPL-ZELUS)/data/slam/particle

bench: bench_per_particles bench_per_steps bench_mem_ideal

bench_per_particles: $(NAME).opt
	time cat ../data | ./$(NAME).opt \
			-w $(WARMUP) \
			-num-runs $(NUMRUNS) \
			-min-particles $(MIN) \
			-max-particles $(MAX) \
			-incr $(INCR) \
			-perf perf.csv \
			-acc accuracy.csv

bench_per_steps: $(NAME).opt
	time cat ../data | ./$(NAME).opt \
			-w $(WARMUP) \
			-num-runs $(NUMRUNS) \
			-particles $(MAX) \
			-perf-step perf-step.csv \
			-mem-step mem.csv

bench_mem_ideal: $(NAME).opt
	time cat ../data | ./$(NAME).opt \
			-w 0 \
			-num-runs 1 \
			-particles $(MAX) \
			-mem-ideal-step mem-ideal.csv

$(NAME): $(INFERENCE_CMA) $(BENCHLIB_CMA) ../array_misc.ml $(NAME).ml run.ml
	$(OCAMLC) -o $(NAME) -I $(ZLLIB) -I $(INFERLIB) -I $(BENCHLIB) \
		-I .. $+

$(NAME).opt: $(INFERENCE_CMXA) $(BENCHLIB_CMXA) ../array_misc.ml \
		$(NAME).ml run.ml
	$(OCAMLOPT) -o $(NAME).opt -I $(ZLLIB) -I $(INFERLIB) -I $(BENCHLIB) \
		-I .. $+

$(NAME).ml : $(INFERENCE_ZCI) ../array_misc.zci $(NAME).zls
	$(ZELUC) -I $(INFERLIB) -noreduce  -I .. $(NAME).zls

%.zci: %.zli
	$(ZELUC) -I $(INFERLIB) -I .. $<

%.cmo: %.ml
	ocamlc -c -I $(ZLLIB) -I $(INFERLIB) -noreduce $<

$(INFERENCE_CMA):
	$(MAKE) -C $(INFERLIB) inference.cma

$(INFERENCE_CMXA):
	$(MAKE) -C $(INFERLIB) inference.cmxa

$(INFERENCE_ZCI):
	$(MAKE) -C $(INFERLIB) byte

clean:
	-rm -f *.zc*
	-rm -f *.pyc
	-rm -f *.cm* *.o
	-rm -f gen_data.ml
	-rm -f $(NAME).ml
	-rm -f *.pyc

cleanall: clean
	-rm -f $(NAME) $(NAME).opt
	-rm -f gen_data gen_data.opt
	-rm -f *~
