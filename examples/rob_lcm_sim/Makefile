LCM=lcm-gen
GCC=gcc
ZELUC=zeluc
ZFLAGS= -robot -nodeadcode -deps -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus -package graphics 

all: zelus-compile robot-compile

zelus-lcm-gen: ./lcmtypes/robot_store_t.lcm
	$(LCM) --c-cpath lcmtypes/ --c-hpath lcmtypes/ -c ./lcmtypes/robot_store_t.lcm

./lcmtypes/robot_store_t.o: zelus-lcm-gen
	$(GCC) -g `pkg-config --cflags lcm` -c ./lcmtypes/robot_store_t.c -o ./lcmtypes/robot_store_t.o

zelus-ocaml: bot.zls
	$(ZELUC) $(ZFLAGS) bot.zls

zelus-compile: ./lcmtypes/robot_store_t.o zelus-ocaml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o zelus_side.opt drawrobot.ml bot.ml main.ml bot_stubs.c ./lcmtypes/robot_store_t.o -ccopt $(CCLIB)

robot-compile: ./lcmtypes/robot_store_t.o robot_side.c
	$(GCC) -c robot_side.c `pkg-config --cflags lcm`
	gcc -o robot_side ./lcmtypes/robot_store_t.o robot_side.o `pkg-config --libs lcm`
clean: 
	rm lcmtypes/*.c lcmtypes/*.h lcmtypes/*.o *.cmi *.cmx *.o *.zci main.ml bot.ml 
