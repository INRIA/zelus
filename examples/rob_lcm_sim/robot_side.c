#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <lcm/lcm.h>
#include <time.h>
#include "lcmtypes/robot_store_t.h"
#include "hash_tbl.h"

#define TO_ZELUS_CHANNEL  "FROM_ROBOT_SIDE"
#define FROM_ZELUS_CHANNEL  "TO_ROBOT_SIDE"

static void my_handler(const lcm_recv_buf_t *rbuf, const char * channel, 
	const robot_store_t * msg, void * user)
{
	printf("Received message on channel \"%s\":\n", channel);
	printf("writing to table '%s'", msg->command);
	insert_to_table(msg->command, msg->value);
    	publish(msg->command); //publishes whatever it receives from Zélus side (does the job of a perfect sensor in perfect condition).   
}

int main (int argc, char ** argv)
{
	lcm_t * lcm = lcm_create(NULL);
    	if (!lcm)
    		return 1;
	
	robot_store_t_subscribe(lcm, FROM_ZELUS_CHANNEL, &my_handler, NULL);
	while(1)
		lcm_handle(lcm);
		
	lcm_destroy(lcm);
	return 0;
}

int publish (char * str){
    float a = get_value(str);
    lcm_t * lcm2 = lcm_create(NULL);
    if(!lcm2)
	return 1;
    robot_store_t my_msg= {
	.command=str,
	.value=a,
    };
    robot_store_t_publish(lcm2, TO_ZELUS_CHANNEL, &my_msg);	
    lcm_destroy(lcm2);
    return 0;
}
