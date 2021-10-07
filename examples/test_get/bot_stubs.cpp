#include <iostream>
#include <unordered_map>
extern "C" {
 #include <stdio.h>
 #include <caml/mlvalues.h>
 #include <caml/memory.h>
 #include <caml/alloc.h>//to create structured ocaml objects (for e.g., to encode a cpp double into an ocaml value type)
 #include <string.h>
}
std::unordered_map<std::string, float> table;
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
  std::string key= String_val(command);
  float val= Double_val(magnitude);
  table[key]=val;
  //std::cout<<"Inside robot_store*->*"<<cmd;
  CAMLreturn (Val_unit);
}
extern "C" value robot_get_cpp(value var){
  CAMLparam1 (var);
  CAMLlocal1 (v_res);
  std::string key= String_val(var);
  //std::cout<< "Inside robot_get!<->"<<key;
  float val;
  if (table.find(key) == table.end())
  	val=0.0;
  else
  	val=table[key];
  v_res= caml_copy_double(val);
  CAMLreturn (v_res);
}








