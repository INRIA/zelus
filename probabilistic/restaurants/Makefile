NAME=restaurant

all: $(NAME)

$(NAME): ../ztypes.cmo ../distribution.ml ../normalize.ml ../infer.ml \
	../gridworld/gridworld.ml restaurant_world.ml \
	$(NAME).ml main.ml
	ocamlc -o $(NAME) -I .. -I ../gridworld graphics.cma \
               ../distribution.ml ../normalize.ml ../infer.ml \
	       ../gridworld/gridworld.ml restaurant_world.ml \
               $(NAME).ml main.ml

$(NAME).ml main.ml:  ../distribution.zci ../infer.zci \
		../gridworld/gridworld.zci restaurant_world.zci \
		$(NAME).zls
	zeluc -I .. -I ../gridworld -s main $(NAME).zls

%.zci: %.zli
	zeluc -I .. -I ../gridworld $<

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
