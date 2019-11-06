INFERLIB=../../inference
OWLLIB=../../owl
ZELUC=zeluc -copy -I $(INFERLIB) -I $(OWLLIB)

ZLI=$(wildcard *.zli)
ZCI=$(ZLI:zli=zci)

NAME=naive_bayes_german

all: build

$(NAME).ml main.ml: $(ZCI) $(NAME).zls
	$(ZELUC) -s main $(NAME).zls

clean:
	rm -f $(NAME).ml main.ml
	rm -f *.zci

## Generic rules

.phony: build exec

exec: main.ml
	dune exec ./main.exe

build: main.ml
	dune build main.exe

%.zci: %.zli
	$(ZELUC) $<

cleanall: clean
	dune clean
	rm -f *~

