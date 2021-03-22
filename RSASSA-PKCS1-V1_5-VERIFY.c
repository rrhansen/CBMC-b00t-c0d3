#include "sha2-256.h"
#include "RSASSA-PKCS1-V1_5-VERIFY.h"
#include "memory.h"

char* __hash_message; 

int32_t* RSA_3072_ENCRYPT(char* data, int size, int32_t exponent, int32_t* modulus){
  
  __CPROVER_assert(data == __hash_message,
  "PROPERTY 5: The data to be encrypted is == to the computed hash");    
  
  int32_t* encrypt = malloc(size);
  return encrypt;
}


int RSASSA_PKCS1_V1_5_VERIFY(int32_t exponent, int32_t* modulus, char* message, int message_len, int32_t* signature, rom_ext_manifest_t __current_rom_ext_mf){
   __CPROVER_assert(__CPROVER_OBJECT_SIZE(signature) * 8 == RSA_SIZE * 32,
  "PROPERTY 5: Signature to be verified is 3072-bits.");

  __CPROVER_assert(sizeof(exponent) * 8 == 32,
  "PROPERTY 5: Public key exponent is 32 bits.");

  __CPROVER_assert((sizeof(pub_key_t) - sizeof(exponent)) * 8 == RSA_SIZE*32,
  "PROPERTY 5: Public key modulus is 3072-bits.");    

  __REACHABILITY_CHECK

  char* hash = SHA2_256(message, message_len, __current_rom_ext_mf); //message_len in bytes

  __hash_message = hash; //for PROPERTY 5

  __CPROVER_assert(__CPROVER_OBJECT_SIZE(hash)==256/8, 
  "PROPERTY 3: Hash is 256 bits");   

  __CPROVER_assert(__CPROVER_r_ok(hash, 256/8),
  "PROPERTY 3: hash is in readable address");  

  int32_t* encrypt = RSA_3072_ENCRYPT(hash, RSA_SIZE*sizeof(int32_t), exponent, modulus);

  if(memcmp(signature, encrypt, RSA_SIZE*sizeof(int32_t))==0)
    return 1; //verified
  else
    return 0;
}

