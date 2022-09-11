#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <lcm/lcm.h>
#include <time.h>
#include "lcmtypes/robot_store_t.h"

#define MBOT_MOTOR_TRANSVERSE_CHANNEL  "MBOT_MOTOR_TRANSVERSE"

int main (int argc, char ** argv){
	lcm_t * lcm = lcm_create(NULL);
	if(!lcm)
		return 1;
	robot_store_t my_msg= {
		.command="my_command",
		.value=23.0,
	};
	robot_store_t my_msg2= {
		.command="my_cmd",
		.value=42.1,
	};
	//my_cmd.utime = (unsigned long)time(NULL);
    // Need to divide by 100 and convert to float since motor speeds come in as hundredths of units (and as integer arguments)
    //for (int i=0; i<5; i++){
    //	if (i%2 ==0){
   		robot_store_t_publish(lcm, "MBOT_MOTOR_TRANSVERSE", &my_msg);
   	//	printf("Message %d published!\n", i+1);
   	//}
   	//else{
   	//	robot_store_t_publish(lcm, "MBOT_MOTOR_TRANSVERSE", &my_msg2);
   	//	printf("Message %d published!\n", i+1);}
   //} 
   	
   	lcm_destroy(lcm);
   	return 0;
}   	
