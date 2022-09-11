#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <lcm/lcm.h>
#include "example_t.h"
//#include "robot_store_t.h"
#include <time.h>

//#define MBOT_MOTOR_TRANSVERSE_CHANNEL "MBOT_MOTOR_TRANSVERSE"

// Sends motor commands to the robot
float a=1.0;
CAMLprim value 
robot_get_cpp(value var)
{
    //std::string key = String_val(var);
    //printf("Command: %s\n", (String_val(var)));
    //printf("%f", a);
    return caml_copy_double(a);
}

CAMLprim value
move_robot_cpp(value speed){
	lcm_t * lcm = lcm_create(NULL);
	example_t cmd;
	cmd.utime = (unsigned long)time(NULL);
	cmd.trans_v = Int_val(speed)/100.0;
	cmd.angular_v = 0.;
	example_t_publish(lcm, "EXAMPLE", &cmd);
	lcm_destroy(lcm);
	return Val_unit;
}

CAMLprim value
robot_store_c(value cmd,value mag){
	return Val_unit;
}

CAMLprim value
control_robot_c(value t_speed, value a_speed){
	return Val_unit;
}

CAMLprim value
robot_str_cpp (value cmd, value mag){
	return Val_unit;
}
