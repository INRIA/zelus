#include "publisher.h"
//int trans_v=30;
//int main(int argc, char **argv) {
//	ros::init(argc, argv, "test_stubs");
//	ros::NodeHandle n;
//	ros::Publisher pub = n.advertise<std_msgs::String>("message", 1000);
//	ros::Rate loop_rate(10);
//	int count = 0;
//	while (ros::ok()) {
//		std_msgs::String msg;
//		std::stringstream ss;
//		ss << "Input vel is "<<trans_v<<" message number "<< count;
//		msg.data = ss.str();
//		ROS_INFO("%s", msg.data.c_str());
//		pub.publish(msg);
//		ros::spinOnce();
//		loop_rate.sleep();
//		++count;
//	}
//	return 0;
//}

int main(int argc, char **argv){
	ros::init(argc, argv, "publisher");
	ros::NodeHandle nh;
	init(nh);
	return 0;
}
int init(ros::NodeHandle n){
    ros::NodeHandle nh = n;
    cycle_rate = 10;
    // Publisher
    pub = nh.advertise<std_msgs::String>("message", 1000);
    // Spin the node
    run();
    
}
int count=0;
void run(){
    // Sets refesh rates
    ros::Rate loop_rate(cycle_rate);
    cycles = 0;

    while(ros::ok()){
        // End of cycle
        cycles++;
        count=cycles;
        loop_rate.sleep();
        ros::spinOnce();
    }

    ROS_INFO("Cleaning up zel_to_hub layer...");
}

void publish_speed(int vel){
	std_msgs::String msg;
	std::stringstream ss;
	ss << "Input vel is "<<vel<<" message number "<< count;
	msg.data= ss.str();
	ROS_INFO("%s", msg.data.c_str());
	pub.publish(msg);	
}
