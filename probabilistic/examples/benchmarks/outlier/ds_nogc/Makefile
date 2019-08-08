PPL-ZELUS=$(HOME)/probabilistic/mit-ibm/ppl-zelus
ZELUC=zeluc
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

NAME=outlier_ds_nogc
MIN=100
MAX=100
INCR=2
CSV_FILES=perf.csv perf-step.csv mem.csv accuracy.csv

all: opt

.PHONY: $(INFERENCE_CMA) $(INFERENCE_CMXA) $(BENCHLIB_CMA) $(BENCHLIB_CMXA) \
	bench publish

byte: $(NAME)
opt: $(NAME).opt

publish:
	cp perf-step.csv mem.csv $(PPL-ZELUS)/data/outlier/ds_nogc

bench: $(NAME).opt
	time cat ../data | ./$(NAME).opt \
			-min-particles $(MIN) \
			-max-particles $(MAX) \
			-incr $(INCR) \
			-perf perf.csv \
			-perf-step perf-step.csv \
			-mem-step mem.csv \
			-acc accuracy.csv


$(NAME): $(INFERENCE_CMA) $(BENCHLIB_CMA) $(NAME).ml run.ml
	$(OCAMLC) -o $(NAME) -I $(ZLLIB) -I $(INFERLIB) -I $(BENCHLIB) \
		$(INFERENCE_CMA) $(BENCHLIB_CMA) \
		$(NAME).ml run.ml

$(NAME).opt: $(INFERENCE_CMXA) $(BENCHLIB_CMXA) $(NAME).ml run.ml
	$(OCAMLOPT) -o $(NAME).opt -I $(ZLLIB) -I $(INFERLIB) -I $(BENCHLIB) \
		$+

$(NAME).ml : $(INFERENCE_ZCI) $(NAME).zls
	zeluc -I $(INFERLIB) -noreduce $(NAME).zls

%.zci: %.zli
	zeluc -I $(INFERLIB) $<

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
