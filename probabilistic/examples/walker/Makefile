ZELUC=zeluc
ZLLIB=$(shell $(ZELUC) -where)
INFERLIB=../../inference

INFERENCE_CMA=$(INFERLIB)/inference.cma
INFERENCE_CMXA=$(INFERLIB)/inference.cmxa
INFERENCE_ZCI=$(INFERLIB)/distribution.zci $(INFERLIB)/infer.zci

OCAMLDEP=ocamldep
OCAMLC=ocamlc -g
OCAMLOPT=ocamlopt

NAME=walker

all: byte opt

.PHONY: $(INFERENCE_CMA) $(INFERENCE_CMXA)

byte: $(NAME)
opt: $(NAME).opt

$(NAME): $(INFERENCE_CMA) $(NAME).ml main.ml walker_misc.ml
	$(OCAMLC) -o $(NAME) -I $(ZLLIB) -I $(INFERLIB) \
		$(INFERENCE_CMA) \
		walker_misc.ml $(NAME).ml main.ml

$(NAME).opt: $(INFERENCE_CMXA) $(NAME).ml main.ml walker_misc.ml
	$(OCAMLOPT) -o $(NAME).opt -I $(ZLLIB) -I $(INFERLIB) \
		$(INFERENCE_CMXA) \
		walker_misc.ml $(NAME).ml main.ml

$(NAME).ml main.ml: $(INFERENCE_ZCI) walker_misc.zci $(NAME).zls
	zeluc -I $(INFERLIB) -s main $(NAME).zls

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
	-rm -f $(NAME).ml main.ml

cleanall: clean
	-rm -f $(NAME) $(NAME).opt
	-rm -f *~
