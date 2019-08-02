ZELUC=zeluc
ZLLIB=$(shell $(ZELUC) -where)
INFERLIB=../../../../inference

INFERENCE_CMA=$(INFERLIB)/inference.cma
INFERENCE_CMXA=$(INFERLIB)/inference.cmxa
INFERENCE_ZCI=$(INFERLIB)/distribution.zci $(INFERLIB)/infer.zci

OCAMLDEP=ocamldep
OCAMLC=ocamlc -g
OCAMLOPT=ocamlopt

NAME=kalman_ds_nogc

all: opt

.PHONY: $(INFERENCE_CMA) $(INFERENCE_CMXA)

byte: $(NAME)
opt: $(NAME).opt

$(NAME): $(INFERENCE_CMA) $(NAME).ml aux.ml run.ml
	$(OCAMLC) -o $(NAME) -I $(ZLLIB) -I $(INFERLIB) \
		$(INFERENCE_CMA) \
		aux.ml $(NAME).ml run.ml

$(NAME).opt: $(INFERENCE_CMXA) $(NAME).ml aux.ml
	$(OCAMLOPT) -o $(NAME).opt -I $(ZLLIB) -I $(INFERLIB) \
		$(INFERENCE_CMXA) \
		aux.ml $(NAME).ml run.ml

$(NAME).ml: $(INFERENCE_ZCI) aux.zci $(NAME).zls
	zeluc -I $(INFERLIB) -noreduce $(NAME).zls

%.zci: %.zli
	zeluc -I $(INFERLIB) $<

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
	-rm -f $(NAME).ml 
	-rm -f gen_data.ml 

cleanall: clean
	-rm -f $(NAME) $(NAME).opt
	-rm -f gen_data gen_data.opt
	-rm -f *~
