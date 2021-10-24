#include <iostream>
#include <unordered_map>
extern "C" {
 #include <stdio.h>
 #include <caml/mlvalues.h>
 #include <caml/memory.h>
 #include <caml/alloc.h>//to create structured ocaml objects (for e.g., to encode a cpp double into an ocaml value type)
 #include <string.h>
}

extern "C" value move_robot_cpp(value speed){
  CAMLparam1 (speed);
  CAMLreturn (Val_unit);
}

extern "C" value control_robot_c(value t_speed, value a_speed){
  CAMLparam2 (t_speed, a_speed);
  CAMLreturn (Val_unit);
}
extern "C" value robot_store_c(value command, value magnitude){
  CAMLparam2 (command, magnitude);
  
  CAMLreturn (Val_unit);
}
extern "C" value robot_str_cpp(value command, value magnitude){
  CAMLparam2 (command, magnitude);
  printf("Command: %s\n", (String_val(command)));
	printf("Magnitude: %f\n", (Double_val(magnitude)));
  CAMLreturn (Val_unit);
}
extern "C" value robot_get_cpp(value var){
  CAMLparam1 (var);
  CAMLlocal1 (v_res);
  
  CAMLreturn (v_res);
}








