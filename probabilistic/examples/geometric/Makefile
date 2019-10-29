INFERLIB=../../inference
ZELUC=zeluc -copy -I $(INFERLIB)

NAME=geometric

all: build

$(NAME).ml main.ml: $(NAME).zls
	$(ZELUC) -s main $+

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
