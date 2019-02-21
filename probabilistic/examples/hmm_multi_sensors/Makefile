ZELUC=zeluc
ZLLIB=$(shell $(ZELUC) -where)
INFERLIB=../../inference

INFERENCE_CMA=$(INFERLIB)/inference.cma
INFERENCE_CMXA=$(INFERLIB)/inference.cmxa
INFERENCE_ZCI=$(INFERLIB)/distribution.zci $(INFERLIB)/infer.zci

OCAMLDEP=ocamldep
OCAMLC=ocamlc
OCAMLOPT=ocamlopt

NAME=hmm_multi_sensors

all: opt

.PHONY: $(INFERENCE_CMA) $(INFERENCE_CMXA)

byte: $(NAME)
opt: $(NAME).opt

$(NAME): $(INFERENCE_CMA) display.ml $(NAME).ml main.ml
	$(OCAMLC) -o $(NAME) -I $(ZLLIB) -I $(INFERLIB) \
		$(INFERENCE_CMA) unix.cma graphics.cma \
		display.ml $(NAME).ml main.ml

$(NAME).opt: $(INFERENCE_CMXA) display.ml $(NAME).ml main.ml
	$(OCAMLOPT) -o $(NAME).opt -I $(ZLLIB) -I $(INFERLIB) \
		$(INFERENCE_CMXA) unix.cmxa graphics.cmxa  \
		display.ml $(NAME).ml main.ml

$(NAME).ml main.ml: $(INFERENCE_ZCI) display.zci $(NAME).zls
	zeluc -I $(INFERLIB) -sampling 0.02 -s main $(NAME).zls

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
