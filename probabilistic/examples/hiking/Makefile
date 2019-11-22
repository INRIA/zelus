INFERLIB=../../inference
ZELUC=zeluc -copy -I $(INFERLIB)

ZLI=../gridworld/gridworld.zli $(wildcard *.zli)
ZCI=$(ZLI:zli=zci)

NAME=hiking


all: build

$(NAME).ml main.ml: $(ZCI) $(NAME).zls
	$(ZELUC) -I ../gridworld -s main $(NAME).zls

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
	$(ZELUC) -I ../gridworld $<

cleanall: clean
	dune clean
	rm -f *~
