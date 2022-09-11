#include <stdio.h>
#include <inttypes.h>
#include <lcm/lcm.h>
#include "example_t.h"
static void
my_handler(const lcm_recv_buf_t *rbuf, const char * channel, 
        const example_t * msg, void * user)
{
    int i;
    printf("Received message on channel \"%s\":\n", channel);
    printf("  utime   = %"PRId64"\n", msg->utime);
    printf("  t_speed    = (%f)\n",
            msg->trans_v);
    printf("  a_speed    = (%f)\n",
            msg->angular_v);
}
int
main(int argc, char ** argv)
{
    lcm_t * lcm = lcm_create(NULL);
    if(!lcm)
        return 1;
    example_t_subscribe(lcm, "EXAMPLE", &my_handler, NULL);
    while(1)
        lcm_handle(lcm);
    lcm_destroy(lcm);
    return 0;
}
