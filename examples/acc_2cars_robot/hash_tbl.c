#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "hash_tbl.h"
int count=0;
HashItem* hashTable[SIZE];

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
        // If we arrive at the element, update it
		if(strcmp(hashTable[index]->command,cmd)==0){
			hashTable[index]->value=val;
			//printf("updated successfully!");
			return;
		}
            //Otherwise, there's a hash collision, so we increment (and possibly wrap around) until we find an empty spot
        	++index;
      		index%= SIZE;
   	}
    // If we're here, we need to create a new hash table entry (we couldn't find an already stored entry)
    HashItem* item = (struct HashItem*) malloc(sizeof(HashItem));
	item->command=(char*) malloc(strlen(cmd)+1);
	strcpy(item->command, cmd);
	item->value=val;
   	hashTable[index] = item;
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

