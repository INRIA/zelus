#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
//#include <lcm/lcm.h>
//#include "robot_store_t.h"
#include <time.h>

//#define MBOT_MOTOR_TRANSVERSE_CHANNEL "MBOT_MOTOR_TRANSVERSE"

// Sends motor commands to the robot
CAMLprim value 
robot_get_c(value var)
{
        
	printf("Command: %f\n", (Double_val(var)));

    return Val_unit;

}

CAMLprim value
move_robot_cpp(value speed){
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
