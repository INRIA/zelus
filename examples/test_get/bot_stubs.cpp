#include <iostream>
extern "C" {
 #include <stdio.h>
 #include <caml/mlvalues.h>
 #include <caml/memory.h>
 #include <caml/alloc.h>//to create structured ocaml objects (for e.g., to encode a cpp double into an ocaml value type)
 #include <string.h>
}
std::string keys[5]={""};
float values[5]={0.0};
std::string cmd="";
float a=0.0;
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
  //for(int i=0;i<sizeof(keys);i++){
  //	if(keys[i]==""||keys[i]==key){
  //		keys[i]=key;
  //		values[i]= val;
  //	}
  //}
  cmd=key;
  a=val;
  //std::cout<<"Inside robot_store*->*"<<cmd;
  CAMLreturn (Val_unit);
}
extern "C" value robot_get_cpp(value var){
  CAMLparam1 (var);
  CAMLlocal1 (v_res);
  std::string key= String_val(var);
  //std::cout<< "Inside robot_get!<->"<<key;
  float val;
  //for(int i=0;i<sizeof (keys);i++){
	//if (keys[i]==""||keys[i]==key){
//		val=values[i];
//	}
//	else if (i==(sizeof(keys)-1)){
//		val=0.0;
//	}
  //}
  if (key==cmd){
  val =a;
  }
  else {
  val =0.0;
  }
  v_res= caml_copy_double(val);
  CAMLreturn (v_res);
}








