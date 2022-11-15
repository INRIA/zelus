#ifndef HASH_TBL_H_
#define HASH_TBL_H_

#include <stdio.h>
#include <string.h>
#define SIZE 20
typedef struct HashItem{
	char* command;
	//char* channel;
	float value;
} HashItem;

struct HashItem* hashTable[SIZE];
int hash_function(const char* str);
void insert_to_table(const char* cmd, float val);
float get_value(const char* cmd);
#endif
