#include "ros/ros.h"
#include "std_msgs/String.h"
void messageCallback(const std_msgs::String::ConstPtr& msg) {
	ROS_INFO("The message I received was: [%s]", msg->data.c_str());
}
int main(int argc, char **argv) {
	ros::init(argc, argv, "simple_subscriber_node");
	ros::NodeHandle n;
	ros::Subscriber sub = n.subscribe("message", 1000, messageCallback);
	ros::spin();
	return 0;
}
