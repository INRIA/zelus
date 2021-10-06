#include <iostream>
#include "publisher.h"
//#include "ros/ros.h"
//#include "std_msgs/String.h"
//#include <sstream>

extern "C" {
	#include <stdio.h>
	#include <caml/mlvalues.h>
	#include <caml/memory.h>
	#include <string.h>
}
int trans_v=0;
extern "C" value move_robot_cpp(value speed){
	CAMLparam1 (speed);
	trans_v= Int_val(speed);
	publish_speed(trans_v);
	//std::cout<< "Inside cpp!" <<trans_v;
	//printf("%d\n", trans_v);
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

