#include <iostream>
extern "C" {
 #include <caml/memory.h>
 #include <caml/mlvalues.h>
 
}

extern "C" value move_robot_c(value speed){
 CAMLparam1 (speed);
 std::cout<< "Hi there !" <<Int_val(speed);
 CAMLreturn (Val_unit);
}
