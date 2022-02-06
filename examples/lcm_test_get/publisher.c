#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <lcm/lcm.h>
#include <time.h>
#include "lcmtypes/robot_store_t.h"

#define MBOT_MOTOR_TRANSVERSE_CHANNEL  "MBOT_MOTOR_TRANSVERSE"

void main(){
	lcm_t * lcm = lcm_create(NULL);
	robot_store_t my_cmd;
	//my_cmd.utime = (unsigned long)time(NULL);
    // Need to divide by 100 and convert to float since motor speeds come in as hundredths of units (and as integer arguments)
        my_cmd.command = "my_command";
        my_cmd.value = 23.0;
   	robot_store_t_publish(lcm, "MBOT_MOTOR_TRANSVERSE", &my_cmd); 
   	lcm_destroy(lcm);
}   	
