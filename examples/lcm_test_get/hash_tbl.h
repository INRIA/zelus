#ifndef HASH_TBL_H_
#define HASH_TBL_H_

#include <stdio.h>
#include <string.h>
#define SIZE 20
int count=0;
struct HashItem{
	char* command;
	//char* channel;
	float value;
};

struct HashItem* hashTable[SIZE];

int hash_function(const char* str) {
	int i = 0;
	for (int j=0; str[j]!=0; j++)
        	i += str[j];
	return (i % SIZE);
}

void insert_to_table(const char* cmd, float val){
	int index = hash_function (cmd);
	//int first_index=(index-1)%SIZE;	
	while(hashTable[index] != NULL) {	//while(hashTable[index] != NULL&&index!=first_index)... becomes handy in the case where the table might become full.
		if(strcmp(hashTable[index]->command,cmd)==0){
			hashTable[index]->value=val;
			//printf("updated successfully!");
			return;
		}
        	++index;
      		index%= SIZE;
   	}
	struct HashItem* item = (struct HashItem*) malloc(sizeof(struct HashItem));
	item->command=(char*) malloc(strlen(cmd)+1);
	strcpy(item->command, cmd);
	item->value=val;
	//char* uppercase[strlen(cmd)+1];
	//for (int j=0; cmd[j]!='\0';j++){
	//	if(str[i]>='a' && str[i]<='z')
	//		uppercase[j]= cmd[j]-32;
	//	else
	//		uppercase[j]=cmd[j];
	//}
	//item->channel=(char*) malloc(strlen(uppercase)+1);
   	hashTable[index] = item;
   	//printf("New variable inserted successfully!");
   	count++;
}

float get_value(const char* cmd){
	if (count==0)
		return 0.0;
	int index=hash_function(cmd);
	int first_index=(index-1)%SIZE;
	while(hashTable[index]!=NULL&&index!=first_index){
		if(strcmp(hashTable[index]->command,cmd)==0){
			return hashTable[index]->value;
		}
		++index;
      		index%= SIZE;	
	}
	if (index==first_index&&strcmp(hashTable[index]->command,cmd)==0)
		return hashTable[index]->value;
	return 0.0;//that value was not stored in the table. i.e., it's value is zero
}

#endif
