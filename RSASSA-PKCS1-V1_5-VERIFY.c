#include "sha2-256.h"
#include "RSASSA-PKCS1-V1_5-VERIFY.h"
#include "memory.h"


int32_t* RSA_3072_ENCRYPT(){
  int32_t* encrypt = malloc(RSA_SIZE*sizeof(int32_t));
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

  __CPROVER_assert(__CPROVER_OBJECT_SIZE(hash)==256/8, 
  "PROPERTY 3: Hash is 256 bits");   

  __CPROVER_assert(__CPROVER_r_ok(hash, 256/8),
  "PROPERTY 3: hash is in readable address");  

  int32_t* encrypt = RSA_3072_ENCRYPT();

  if(memcmp(signature, encrypt, RSA_SIZE*sizeof(int32_t))==0)
    return 1; //verified
  else
    return 0;
}

