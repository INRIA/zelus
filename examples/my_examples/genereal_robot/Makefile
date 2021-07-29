all: bot.ml main.ml bot_stubs.o robot_store_t.o 
	#ocamlfind ocamlopt -linkpkg -package zelus bot_stubs.o robot_store_t.o bot.ml main.ml
	#ocamlfind ocamlopt -I /usr/local/include/ -linkpkg -package zelus bot.ml main.ml bot_stubs.c robot_store_t.c -ccopt "-g `pkg-config --libs lcm`"
	ocamlfind ocamlopt -I /usr/local/include/ -linkpkg -package zelus bot.ml main.ml bot_stubs.c -ccopt "-g `pkg-config --libs lcm`"

bot_stubs.o: bot_stubs.c robot_store_t.o 
	ocamlopt robot_store_t.o bot_stubs.c -ccopt "-g `pkg-config --cflags lcm`"

bot.ml main.ml: bot.zls
	zeluc -robot -nodeadcode -s main bot.zls

robot_store_t.o: robot_store_t.c robot_store_t.h
	gcc -g `pkg-config --cflags lcm` -c robot_store_t.c

robot_store_t.c robot_store_t.h: robot_store_t.lcm
	lcm-gen -c --c-typeinfo robot_store_t.lcm

clean:
	rm *.cmi *.cmx main.ml bot.ml *.o *.out *.zci robot_store_t.c robot_store_t.h
	
	
	
	

