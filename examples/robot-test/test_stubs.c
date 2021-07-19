#include <stdio.h>
#include <caml/mlvalues.h>
#include <lcm/lcm.h>
#include "mbot_motor_command_t.h"
#include <time.h>

#define MBOT_MOTOR_COMMAND_CHANNEL "MBOT_MOTOR_COMMAND"

// Sends motor commands to the robot
CAMLprim value
move_robot_c(value speed, value t_speed){
	lcm_t * lcm = lcm_create("udpm://239.255.76.67:7667?ttl=1");
     mbot_motor_command_t cmd;
    cmd.utime = (unsigned long)time(NULL);
    // Need to divide by 100 and convert to float since motor speeds come in as hundredths of units (and as integer arguments)
    cmd.trans_v = Int_val(speed)/100.0;
	cmd.angular_v = 0.;
    mbot_motor_command_t_publish(lcm, MBOT_MOTOR_COMMAND_CHANNEL, &cmd);
	lcm_destroy(lcm);
    return Val_unit;

}

