#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <lcm/lcm.h>
#include "robot_store_t.h"
#include "hash_tbl.h"
#include <time.h>

//#define MBOT_MOTOR_TRANSVERSE_CHANNEL "MBOT_MOTOR_TRANSVERSE"

// Sends motor commands to the robot
float a;

CAMLprim value 
robot_get_cpp(value var)
{
    //std::string key = String_val(var);
    //printf("Command: %s\n", (String_val(var)));
    a=get_value(String_val(var));
    //printf("%f", a);
    return caml_copy_double(a);
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
robot_str_cpp(value cmd,value mag){
	insert_to_table(String_val(cmd), Double_val(mag));//Store the variable to the local hash table (it can also be an update to an existing variable)
	lcm_t * lcm = lcm_create(NULL);
	robot_store_t my_cmd;
	my_cmd.utime = (unsigned long)time(NULL);
    // Need to divide by 100 and convert to float since motor speeds come in as hundredths of units (and as integer arguments)
        my_cmd.command = String_val(cmd);
        my_cmd.value = Double_val(mag);
   	robot_store_t_publish(lcm, "MBOT_MOTOR_TRANSVERSE", &my_cmd); 
   	lcm_destroy(lcm);
	return Val_unit;
}

CAMLprim value
control_robot_c(value t_speed, value a_speed){
	return Val_unit;
}
