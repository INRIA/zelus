ZELUC=zeluc
ZLLIB=$(shell $(ZELUC) -where)
INFERLIB=../../../inference
OWLLIB=../../../owl

INFERENCE_CMA=$(INFERLIB)/inference.cma
INFERENCE_CMXA=$(INFERLIB)/inference.cmxa
INFERENCE_ZCI=$(INFERLIB)/distribution.zci $(INFERLIB)/infer.zci

OWL_ZCI=

OCAMLDEP=ocamldep
OCAMLC=ocamlc -g
OCAMLOPT=ocamlopt

NAME=gen_data

all: opt
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
	$(MAKE) -C ds_nogc bench_per_particles
	$(MAKE) -C ds_bounded bench_per_particles

bench_per_steps:
	$(MAKE) -C particles bench_per_steps
	$(MAKE) -C ds bench_per_steps
	$(MAKE) -C ds_nogc bench_per_steps
	$(MAKE) -C ds_bounded bench_per_steps
	$(MAKE) -C ds_bounded bench_per_steps

bench_mem_ideal:
	$(MAKE) -C particles bench_mem_ideal
	$(MAKE) -C ds bench_mem_ideal
	$(MAKE) -C ds_nogc bench_mem_ideal
	$(MAKE) -C ds_bounded bench_mem_ideal

.PHONY: $(INFERENCE_CMA) $(INFERENCE_CMXA) publish bench

byte: $(NAME)
opt: $(NAME).opt

$(NAME): $(INFERENCE_CMA) $(NAME).ml main.ml
	$(OCAMLC) -o $(NAME) -I $(ZLLIB) -I $(INFERLIB) \
		$(INFERENCE_CMA) \
		$(NAME).ml main.ml


$(NAME).opt: $(INFERENCE_CMXA) $(NAME).ml main.ml
	$(OCAMLOPT) -o $(NAME).opt -I $(ZLLIB) -I $(INFERLIB) \
		$(INFERENCE_CMXA) \
		$(NAME).ml main.ml


$(NAME).ml main.ml: $(INFERENCE_ZCI) util.zci $(NAME).zls
	zeluc -I $(INFERLIB) -I $(OWLLIB) -s main $(NAME).zls

%.zci: %.zli
	zeluc -I $(INFERLIB) -I $(OWLLIB) $<

%.cmo: %.ml
	ocamlc -c -I $(ZLLIB) -I $(INFERLIB) $<

$(INFERENCE_CMA):
	$(MAKE) -C $(INFERLIB) inference.cma

$(INFERENCE_CMXA):
	$(MAKE) -C $(INFERLIB) inference.cmxa

$(INFERENCE_ZCI):
	$(MAKE) -C $(INFERLIB) byte

clean:
	-rm -f *.zc*
	-rm -f *.cm* *.o
	-rm -f $(NAME).ml main.ml
	-rm -f gen_data.ml main.ml
	$(MAKE) -C particles clean
	$(MAKE) -C ds clean
	$(MAKE) -C ds_nogc clean

cleanall: clean
	-rm -f $(NAME) $(NAME).opt
	-rm -f gen_data gen_data.opt
	-rm -f *~
	$(MAKE) -C particles cleanall
	$(MAKE) -C ds cleanall
	$(MAKE) -C ds_nogc cleanall
