/*********************************************************************
* Filename:   sha256.c
* Author:     Brad Conte (brad AT bradconte.com)
* Copyright:
* Disclaimer: This code is presented "as is" without any guarantees.
* Details:    Performs known-answer tests on the corresponding SHA1
	          implementation. These tests do not encompass the full
	          range of available test vectors, however, if the tests
	          pass it is very, very likely that the code is correct
	          and was compiled properly. This code also serves as
	          example usage of the functions.
*********************************************************************/

/*************************** HEADER FILES ***************************/
#include <stdio.h>
#include <string.h>
#include "sha2-256.h"
#include <stdlib.h>

/*********************** FUNCTION DEFINITIONS ***********************/


int main()
{
  BYTE text1[] = {"your mom gay"};

  BYTE* hash = sha256(text1, strlen(text1));

  for(int i=0; i<SHA256_BLOCK_SIZE;i++){
    printf("%x",hash[i]);
  }
  printf("\n");
  free(hash);
	return(0);
}