LCM=lcm-gen
GCC=gcc
ZELUC=zeluc
ZFLAGS= -robot -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
DEST=debian@192.168.9.2
DATE="$(shell date)"
# synchronizes time 
SET_DATE="echo $(shell cat ./passwd_roadrunner )| sudo -S date -s ""'""$(DATE)""'"
all: zelus-compile 

robot: remote-build

remote-build: main.ml
	ssh -t $(DEST) $(SET_DATE)
	# transfers over files
	rsync -a ./ --exclude '*.opt' --exclude '*.o' $(DEST):~/kinematic_follower
	ssh -t $(DEST) "eval \$$(opam env); make -C ~/kinematic_follower zelus-compile"

zelus-lcm-gen: ./lcmtypes/robot_store_t.lcm
	$(LCM) --c-cpath lcmtypes/ --c-hpath lcmtypes/ -c ./lcmtypes/robot_store_t.lcm

./lcmtypes/robot_store_t.o: zelus-lcm-gen
	$(GCC) -g `pkg-config --cflags lcm` -c ./lcmtypes/robot_store_t.c -o ./lcmtypes/robot_store_t.o

main.ml: kinematic.zls
	$(ZELUC) $(ZFLAGS) kinematic.zls

zelus-compile: ./lcmtypes/robot_store_t.o main.ml hash_tbl.o
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o zelus_side.opt kinematic.ml main.ml kinematic_stubs.c ./lcmtypes/robot_store_t.o hash_tbl.o -ccopt $(CCLIB)

hash_tbl.o: hash_tbl.c hash_tbl.h
	$(GCC) -c hash_tbl.c -o hash_tbl.o

clean: 
	rm lcmtypes/*.c lcmtypes/*.h lcmtypes/*.o *.cmi *.cmx *.o *.zci main.ml bot.ml 
