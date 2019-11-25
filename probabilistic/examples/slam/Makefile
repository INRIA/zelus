INFERLIB=../../inference
ZELUC=zeluc -copy -I $(INFERLIB)

ZLI=$(wildcard *.zli)
ZCI=$(ZLI:zli=zci)

NAME_PF=slam_pf
NAME_DS=slam_ds
NAME_RB=slam_rb
NAME_2D=slam_2d

all: build

$(NAME_pf).ml main_pf.ml: $(ZCI) $(NAME_PF).zls
	$(ZELUC) -s main_pf $(NAME_PF).zls

$(NAME_DS).ml main_ds.ml: $(ZCI) $(NAME_DS).zls
	$(ZELUC) -s main_ds $(NAME_DS).zls

$(NAME_RB).ml main_rb.ml: $(ZCI) $(NAME_RB).zls
	$(ZELUC) -s main_rb $(NAME_RB).zls
	
$(NAME_2D).ml main_2d.ml: $(ZCI) $(NAME_2D).zls
	$(ZELUC) -s main_2d $(NAME_2D).zls

clean:
	rm -f $(NAME).ml main.ml
	rm -f $(NAME_DS).ml main_ds.ml
	rm -f $(NAME_RB).ml main_rb.ml
	rm -f $(NAME_RB).ml main_2d.ml
	rm -f *.zci

## Generic rules

.phony: build exec

exec: exec_2d

exec_pf: main_pf.ml main_ds.ml main_rb.ml main_2d.ml
	dune exec ./main_pf.exe

exec_ds: main_pf.ml main_ds.ml main_rb.ml main_2d.ml
	dune exec ./main_ds.exe

exec_rb: main_pf.ml main_ds.ml main_rb.ml main_2d.ml
	dune exec ./main_rb.exe
	
exec_2d: main_pf.ml main_ds.ml main_rb.ml main_2d.ml
	dune exec ./main_2d.exe

build: main_pf.ml main_ds.ml main_rb.ml main_2d.ml
	dune build ./main_pf.exe ./main_ds.exe ./main_rb.exe

%.zci: %.zli
	$(ZELUC) $<

cleanall: clean
	dune clean
	rm -f *~
