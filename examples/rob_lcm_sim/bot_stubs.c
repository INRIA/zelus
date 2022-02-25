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
#define FROM_ROBOT_CHANNEL  "FROM_ROBOT_SIDE"
#define TO_ROBOT_CHANNEL  "TO_ROBOT_SIDE"

static void motor_handler(const lcm_recv_buf_t *rbuf, const char * channel, 
        const robot_store_t * msg, void * user)
{
    printf("Received message on channel \"%s\":\n", channel);
    printf("writing to table '%s'", msg->command);
    insert_to_table(msg->command, msg->value);
}

void *lcm_listen(void *param)
{
    robot_store_t_subscription_t *sub = robot_store_t_subscribe(lcm, FROM_ROBOT_CHANNEL, &motor_handler, NULL); 
    printf("Listener Started\n");
    printf("the value of running is %d\n",running);
    while(running)
        lcm_handle(lcm);
    lcm_destroy(lcm);
    printf("Listener Stopped\n");
    return NULL;
}

CAMLprim value 
LCM_start(value unit){
    printf("Starting LCM...\n");
    lcm = lcm_create(NULL);
    if(!lcm)
        return Val_int(1);
    running = 1;
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
    float a=get_value(String_val(var));
    return caml_copy_double(a);
}

CAMLprim value
robot_str_cpp(value cmd,value mag){
    printf("robot store is called\n");
    //insert_to_table(String_val(cmd), Double_val(mag));//Store the variable to the local hash table (it can also be an update to an existing variable)
    lcm_t * lcm2 = lcm_create(NULL);
    robot_store_t my_cmd;
    // Need to divide by 100 and convert to float since motor speeds come in as hundredths of units (and as integer arguments)
    my_cmd.command = String_val(cmd);
    my_cmd.value = Double_val(mag);
    robot_store_t_publish(lcm2, TO_ROBOT_CHANNEL, &my_cmd); 
    lcm_destroy(lcm2);
    return Val_unit;
}
