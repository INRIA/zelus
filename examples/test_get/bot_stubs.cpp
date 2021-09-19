

#include <iostream>
extern "C" {
 #include <stdio.h>
 #include <caml/mlvalues.h>
 #include <caml/memory.h>
}

extern "C" value move_robot_cpp(value speed){
 CAMLparam1 (speed);
 int trans_v= Int_val(speed);
 std::cout<< "Inside cpp!" <<trans_v;
 printf("%d\n", trans_v);
 CAMLreturn (Val_unit);
}

extern "C" value control_robot_c(value t_speed, value a_speed){
CAMLparam1 (t_speed);
CAMLreturn (Val_unit);
}
extern "C" value robot_store_c(value command, value magnitude){
CAMLparam1 (command);
CAMLreturn (Val_unit);
}
extern "C" value robot_get_cpp(value var){
CAMLparam1 (var);
float trans_v= Double_val(var);
 std::cout<< "Inside variable ! \n";

 printf("%f\n", trans_v);
CAMLreturn (Val_unit);
}

