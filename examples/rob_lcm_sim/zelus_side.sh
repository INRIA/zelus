#compile lcm types
lcm-gen -c ./lcmtypes/robot_store_t.lcm
gcc -g `pkg-config --cflags lcm` -c ./lcmtypes/robot_store_t.c
#compile Zélus code
zeluc -robot -nodeadcode -deps -s main bot.zls
#compile OCaml
ocamlfind ocamlopt -linkpkg -package zelus -package graphics -o zelus_side drawrobot.ml bot.ml main.ml bot_stubs.c ./lcmtypes/robot_store_t.o -cclib "-g `pkg-config --libs lcm`"
