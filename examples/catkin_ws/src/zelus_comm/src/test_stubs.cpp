#include "ros/ros.h"
#include "std_msgs/String.h"
#include <sstream>
//extern "C" {
//	#include <caml/mlvalues.h>
//	#include <caml/memory.h>
//}
int trans_v=30;
int main(int argc, char **argv) {
	ros::init(argc, argv, "test_stubs");
	ros::NodeHandle n;
	ros::Publisher pub = n.advertise<std_msgs::String>("message", 1000);
	ros::Rate loop_rate(10);
	int count = 0;
	while (ros::ok()) {
		std_msgs::String msg;
		std::stringstream ss;
		ss << "Input vel is "<<trans_v<<" message number "<< count;
		msg.data = ss.str();
		ROS_INFO("%s", msg.data.c_str());
		pub.publish(msg);
		ros::spinOnce();
		loop_rate.sleep();
		++count;
	}
	return 0;
}
