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

NAME=coin_ds_nogc

all: opt

.PHONY: $(INFERENCE_CMA) $(INFERENCE_CMXA) $(BENCHLIB_CMA) $(BENCHLIB_CMXA) \
	perf.csv perf-step.csv mem.csv accuracy.csv bench publish

byte: $(NAME)
opt: $(NAME).opt

publish: perf-step.csv
	cp $+ $(PPL-ZELUS)/data/coin/ds_nogc

bench: perf-step.csv

perf-step.csv: $(NAME).opt
	cat ../data | ./$(NAME).opt -perf-step -particles 50 > $@



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
