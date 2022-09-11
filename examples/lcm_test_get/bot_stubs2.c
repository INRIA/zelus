#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/threads.h>
#include <pthread.h>
#include <lcm/lcm.h>
#include <time.h>
#include "hash_tbl.h"
#include "lcmtypes/robot_store_t.h"

lcm_t * lcm;
pthread_t lcm_listener; 
int running = 0;
#define MBOT_MOTOR_TRANSVERSE_CHANNEL  "MBOT_MOTOR_TRANSVERSE"

//#define MBOT_MOTOR_TRANSVERSE_CHANNEL "MBOT_MOTOR_TRANSVERSE"

// Sends motor commands to the robot
float a;

static void motor_handler(const lcm_recv_buf_t *rbuf, const char * channel, 
        const robot_store_t * msg, void * user)
{
    //caml_acquire_runtime_system(); 
    //printf("Received message in C\n");
    printf("Received message on channel \"%s\":\n", channel);
    printf("writing to table '%s'", msg->command);
    insert_to_table(msg->command, msg->value);
    //caml_callback3(*caml_named_value("mbot_motor_callback"),
    //                Val_int(msg->utime), 
    //                Val_int((int)msg->left_motor_pwm),
    //                Val_int((int)msg->right_motor_pwm));
    //caml_release_runtime_system();
}

void *lcm_listen(void *param){
    //caml_c_thread_register();
    robot_store_t_subscription_t *sub = robot_store_t_subscribe(lcm, "MBOT_MOTOR_TRANSVERSE", &motor_handler, NULL); 
    printf("Listener Started\n");
    printf("the value of running is %d\n",running);
    while(running)
        lcm_handle(lcm);
    //robot_store_t_unsubscribe(lcm, sub);
    lcm_destroy(lcm);
    printf("Listener Stopped\n");
    //caml_c_thread_unregister();
    return NULL;
}
CAMLprim value 
LCM_start(value unit){
    printf("Starting LCM...\n");
    lcm = lcm_create(NULL);//"udpm://239.255.76.67:7667?ttl=1"
    if(!lcm)
        return Val_int(1);
    running = 1;
    // Launch LCM listener thread
    pthread_create(&lcm_listener, NULL, lcm_listen, NULL);
    return Val_int(0);
}

CAMLprim value 
LCM_stop(value unit){
    printf("Stopping Listener...\n");
    running = 0;
    return Val_unit;
}
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
	//insert_to_table(String_val(cmd), Double_val(mag));//Store the variable to the local hash table (it can also be an update to an existing variable)
	//lcm_t * lcm = lcm_create(NULL);
	//robot_store_t my_cmd;
	//my_cmd.utime = (unsigned long)time(NULL);
    // Need to divide by 100 and convert to float since motor speeds come in as hundredths of units (and as integer arguments)
        //my_cmd.command = String_val(cmd);
        //my_cmd.value = Double_val(mag);
   	//robot_store_t_publish(lcm, "MBOT_MOTOR_TRANSVERSE", &my_cmd); 
   	//lcm_destroy(lcm);
	return Val_unit;
}

CAMLprim value
control_robot_c(value t_speed, value a_speed){
	return Val_unit;
}
