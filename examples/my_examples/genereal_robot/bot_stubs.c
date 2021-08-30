#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <lcm/lcm.h>
#include "robot_store_t.h"
#include <time.h>

#define MBOT_MOTOR_TRANSVERSE_CHANNEL "MBOT_MOTOR_TRANSVERSE"

// Sends motor commands to the robot
CAMLprim value robot_store_c(value pair) //, value magnitude)
{
	printf("Tag value: %d\n", Tag_val(pair));
	printf("Block size: %ld\n", Wosize_val(pair));
	printf("Isblock: %d\n", Is_block(pair));
	
	printf("Command: %s\n", String_val(Field(pair,0)));
	printf("Magnitude: %f\n", Double_val(Field(pair,1)));
	
	//printf("hello world\n");
	//printf("%f\n", Double_val(magnitude));
        //lcm_t * lcm = lcm_create("udpm://239.255.76.67:7667?ttl=1");
        robot_store_t cmd;
        cmd.utime = (unsigned long)time(NULL);
    // Need to divide by 100 and convert to float since motor speeds come in as hundredths of units (and as integer arguments)
        cmd.command = String_val(Field(pair,0));
        cmd.value = Double_val(Field(pair,1));
        printf("CMD object \n cmd.command = %s \n cmd.value = %f \n",cmd.command,cmd.value);
        printf("Comparing strings %d\n",strcmp(cmd.command, "transverse_vel"));
    if (strcmp(cmd.command, "transverse_vel") == 0) {
   	//robot_store_t_publish(lcm, MBOT_MOTOR_TRANSVERSE_CHANNEL, &cmd); 
   	printf("Reached transverse_vel block\n");	
    } 
    printf("exit\n");
   
	//lcm_destroy(lcm);
    return Val_unit;

}

CAMLprim value
move_robot_c(value speed){
	return Val_unit;
}

CAMLprim value
control_robot_c(value t_speed, value a_speed){
	return Val_unit;
}
