gcc -c robot_side.c
gcc -o robot_side ./lcmtypes/robot_store_t.o robot_side.o `pkg-config --libs lcm`
