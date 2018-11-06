NAME=ilmdp

all: $(NAME)

$(NAME): ../ztypes.cmo ../distribution.ml ../normalize.ml ../infer.ml $(NAME).ml main.ml
	ocamlc -o $(NAME) -I .. \
               ../distribution.ml ../normalize.ml ../infer.ml \
               $(NAME).ml main.ml

$(NAME).ml main.ml:  ../distribution.zci ../infer.zci $(NAME).zls
	zeluc -I .. -s main $(NAME).zls

%.zci: %.zli
	zeluc -I .. $<

%.cmo: %.ml
	ocamlc -c $<

clean:
	rm -f *.zc*
	rm -f *.cm*
	rm -f ../*.cm*
	rm -f ../*.zc*
	rm -f $(NAME).ml main.ml

cleanall: clean
	rm -f $(NAME)
