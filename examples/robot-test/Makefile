all: test.ml main.ml test_stubs.o mbot_motor_command_t.o 
	#ocamlfind ocamlopt -linkpkg -package zelus test_stubs.o mbot_motor_command_t.o test.ml main.ml
	ocamlfind ocamlopt -I /usr/local/include/ -linkpkg -package zelus test.ml main.ml test_stubs.c mbot_motor_command_t.c -ccopt "-g `pkg-config --libs lcm`"

test_stubs.o: test_stubs.c mbot_motor_command_t.o 
	ocamlopt mbot_motor_command_t.o test_stubs.c -ccopt "-g `pkg-config --cflags lcm`"

test.ml main.ml: test.zls
	zeluc -robot -nodeadcode -s main test.zls

mbot_motor_command_t.o: mbot_motor_command_t.c mbot_motor_command_t.h
	gcc -g `pkg-config --cflags lcm` -c mbot_motor_command_t.c

mbot_motor_command_t.c mbot_motor_command_t.h: mbot_motor_command_t.lcm
	lcm-gen -c --c-typeinfo mbot_motor_command_t.lcm

clean:
	rm *.cmi *.cmx main.ml test.ml *.o *.out *.zci
