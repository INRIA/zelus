#include <iostream>
#include "ros/ros.h"
#include "std_msgs/String.h"
#include <sstream>

extern "C" {
	#include <caml/mlvalues.h>
	#include <caml/memory.h>
}
int trans_v=0;
extern "C" value move_robot_cpp(value speed){
	CAMLparam1 (speed);
	trans_v= Int_val(speed);
	std::cout<< "Inside cpp!" <<trans_v;
	printf("%d\n", trans_v);
	CAMLreturn (Val_unit);
}
extern "C" value control_robot_c(value t_speed, value a_speed){
	CAMLparam1 (t_speed);
	CAMLreturn (Val_unit);
}
extern "C" value robot_store_c(value command, value magnitude){
	CAMLparam1 (command);
	CAMLreturn (Val_unit);
}
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
