LCM=lcm-gen
GCC=gcc
ZELUC=zeluc
ZFLAGS= -verify -robot -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
DEST=debian@roadrunner-bbb
all: zelus-compile 

robot: remote-build

remote-build: zelus-ocaml
    # synchronizes time 
    DATE=$(date)
    SET_DATE="cat passwd_roadrunner | sudo -S date -s ""'""$(DATE)""'"
	ssh -t $(DEST) $(SET_DATE)
    # transfers over files
    rsync -a ./ $(DEST):~/acc_2cars_robot
    ssh -t $

zelus-lcm-gen: ./lcmtypes/robot_store_t.lcm
	$(LCM) --c-cpath lcmtypes/ --c-hpath lcmtypes/ -c ./lcmtypes/robot_store_t.lcm

./lcmtypes/robot_store_t.o: zelus-lcm-gen
	$(GCC) -g `pkg-config --cflags lcm` -c ./lcmtypes/robot_store_t.c -o ./lcmtypes/robot_store_t.o

zelus-ocaml: acc.zls
	$(ZELUC) $(ZFLAGS) acc.zls

zelus-compile: ./lcmtypes/robot_store_t.o zelus-ocaml hash_tbl.o
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o zelus_side.opt acc.ml main.ml acc_stubs.c ./lcmtypes/robot_store_t.o hash_tbl.o -ccopt $(CCLIB)

hash_tbl.o: hash_tbl.c hash_tbl.h
	$(GCC) -c hash_tbl.c -o hash_tbl.o

clean: 
	rm lcmtypes/*.c lcmtypes/*.h lcmtypes/*.o *.cmi *.cmx *.o *.zci main.ml bot.ml 
