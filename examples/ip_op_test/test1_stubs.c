#include <stdio.h>
#include <caml/mlvalues.h>
#include <time.h>
CAMLprim value
robot_store_op (value chan, value val){
	printf ("%s", "Hi there from c");
	float num= Double_val(val);
	printf ("the channel is %s\n", String_val(chan));
	printf ("the value is %f\n", num);
	return Val_unit;
}
