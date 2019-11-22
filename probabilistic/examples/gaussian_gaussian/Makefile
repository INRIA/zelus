INFERLIB=../../inference
ZELUC=zeluc -copy -I $(INFERLIB)

NAME=gaussian_gaussian
NAME_DS=gaussian_gaussian_ds

all: build

$(NAME).ml main.ml: $(NAME).zls
	$(ZELUC) -s main $+

$(NAME_DS).ml main_ds.ml: $(NAME_DS).zls
	$(ZELUC) -s main_ds $+

clean:
	rm -f $(NAME).ml main.ml
	rm -f $(NAME_DS).ml main_ds.ml
	rm -f *.zci

## Generic rules

.phony: build exec exec_ds

exec: main.ml main_ds.ml
	dune exec ./main.exe

exec_ds: main.ml main_ds.ml
	dune exec ./main_ds.exe

build: main.ml main_ds.ml
	dune build main.exe main_ds.exe

%.zci: %.zli
	$(ZELUC) $<

cleanall: clean
	dune clean
	rm -f *~
