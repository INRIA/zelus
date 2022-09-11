#include <iostream>
//#include <unordered_map>
#include <lcm/lcm-cpp.hpp>
extern "C" {
 #include <stdio.h>
 #include <caml/mlvalues.h>
 #include <caml/memory.h>
 #include <caml/alloc.h>//to create structured ocaml objects (for e.g., to encode a cpp double into an ocaml value type)
 #include <string.h>
}
//std::unordered_map<std::string, float> table;
float a=1.0;
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
  CAMLreturn (Val_unit);
}
extern "C" value robot_get_cpp(value var){
  CAMLparam1 (var);
  CAMLlocal1 (v_res);
  v_res= caml_copy_double(a);
  CAMLreturn (v_res);
}


move_robot_cpp(value speed){
	lcm::LCM lcm;
	example_t cmd;
	cmd.utime = (unsigned long)time(NULL);
	cmd.trans_v = Int_val(speed)/100.0;
	cmd.angular_v = 0.;
	example_t_publish(lcm, "EXAMPLE", &cmd);
	lcm_destroy(lcm);
	return Val_unit;
}








