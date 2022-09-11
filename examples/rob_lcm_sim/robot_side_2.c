#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <lcm/lcm.h>
#include <time.h>
#include "lcmtypes/robot_store_t.h"
#include "hash_tbl.h"

lcm_t * lcm;
pthread_t lcm_listener; 
int running = 0;
//#define MBOT_MOTOR_TRANSVERSE_CHANNEL  "MBOT_MOTOR_TRANSVERSE"

static void motor_handler(const lcm_recv_buf_t *rbuf, const char * channel, 
        const robot_store_t * msg, void * user)
{
    printf("Received message on channel \"%s\":\n", channel);
    printf("writing to table '%s'", msg->command);
    insert_to_table(msg->command, msg->value);
    publish(msg->command);
}

void *lcm_listen(void *param)
{
    robot_store_t_subscription_t *sub = robot_store_t_subscribe(lcm, "MBOT_MOTOR_TRANSVERSE2", &motor_handler, NULL); 
    printf("Listener Started\n");
    printf("the value of running is %d\n",running);
    while(running)
        lcm_handle(lcm);
    lcm_destroy(lcm);
    printf("Listener Stopped\n");
    return NULL;
}

int 
LCM_start(){
    printf("Starting LCM...\n");
    lcm = lcm_create(NULL);
    if(!lcm)
        return 1;
    running = 1;
    pthread_create(&lcm_listener, NULL, lcm_listen, NULL);
    return 0;
}

void
LCM_stop(){
    printf("Stopping Listener...\n");
    running = 0;
    return;
}

int main (int argc, char ** argv){
    LCM_start();
    //call lcm stop after some condition (time)
    return 0;
}
int publish (char * str){// check const char
    float a = get_value(str);
    lcm_t * lcm2 = lcm_create(NULL);
    if(!lcm2)
	return 1;
    robot_store_t my_msg= {
	.command=str,
	.value=a,
    };
    robot_store_t_publish(lcm2, "MBOT_MOTOR_TRANSVERSE", &my_msg);	
    lcm_destroy(lcm2);
    return 0;
}


