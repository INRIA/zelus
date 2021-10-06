#ifndef PUBLISHER_H_
#define PUBLISHER_H_

#include "ros/ros.h"
#include "std_msgs/String.h"
#include <sstream>

//ros::NodeHandle nh;

int cycle_rate;
int cycles;
ros::Publisher pub;

int init(ros::NodeHandle n);

void run();

void publish_speed(int vel);

#endif
