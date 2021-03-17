#include "verify.h"
#include "mask_rom.h"
#include "sha2-256.h"

rom_ext_manifest_t __current_rom_ext_mf;


extern char* HASH(char* message, int size){
  int __expected_size = 
    sizeof(__current_rom_ext_mf.pub_signature_key)+sizeof(__current_rom_ext_mf.image_length)+__current_rom_ext_mf.image_length;
  
  __CPROVER_assert(memcmp(
      message, 
      &__current_rom_ext_mf.pub_signature_key, 
      sizeof(__current_rom_ext_mf.pub_signature_key)) == 0,
      "PROPERTY 4: Message contains the key");

  __CPROVER_assert(memcmp(
      message + sizeof(__current_rom_ext_mf.pub_signature_key),
      &__current_rom_ext_mf.image_length,
      sizeof(__current_rom_ext_mf.image_length)) == 0,
      "PROPERTY 4: Message contains the Image length");

  __CPROVER_assert(memcmp(
      message + sizeof(__current_rom_ext_mf.pub_signature_key) + sizeof(__current_rom_ext_mf.image_length),
      __current_rom_ext_mf.image_code,
      __current_rom_ext_mf.image_length) == 0,
      "PROPERTY 4: Message contains the Image code");
     
  __CPROVER_assert(size == __expected_size,
  "PROPERTY 4: Hash size parameter is as expected.");
 
  __CPROVER_assert(__CPROVER_OBJECT_SIZE(message) == __expected_size,
  "PROPERTY 4: Size of message is as expected.");
  
  char* hash;

  hash = sha256(message, size);
  
  __CPROVER_assert(__CPROVER_OBJECT_SIZE(hash)==256/8, 
  "PROPERTY 3: Hash is 256 bits");   

  __CPROVER_assert(__CPROVER_r_ok(hash, 256/8),
  "PROPERTY 3: hash is in readable address");
  
  __REACHABILITY_CHECK

  return hash;
}


extern int RSA_VERIFY(pub_key_t pub_key, char* message, signature_t signature) {
    __CPROVER_assert(__CPROVER_OBJECT_SIZE(signature.value) * 8 == RSA_SIZE * 32,
    "PROPERTY 5: Signature to be verified is 3072-bits.");

    __CPROVER_assert(__CPROVER_OBJECT_SIZE(message) * 8 == 256,
    "PROPERTY 5: Message to compare should be a 256 bit value.");

    __CPROVER_assert(__CPROVER_OBJECT_SIZE(pub_key.modulus) * 8 == RSA_SIZE * 32 + 32,
    "PROPERTY 5: Public key modulus is 3072-bits and exponent is 32 bits.");

    __REACHABILITY_CHECK
}


int verify_rom_ext_signature(pub_key_t rom_ext_pub_key, rom_ext_manifest_t manifest) {
  __CPROVER_precondition(MAX_IMAGE_LENGTH >  manifest.image_length && manifest.image_length > 0, 
  "Precondition: Assumes rom ext image code is < 10 and > 0");

  __CPROVER_precondition(__CPROVER_r_ok(manifest.image_code, manifest.image_length), 
  "Precondition: Assumes rom ext image code is readable");

  __current_rom_ext_mf = manifest; //for cbmc PROPERTY 4

  int bytes = 
    sizeof(manifest.pub_signature_key)+sizeof(manifest.image_length)+manifest.image_length;

  char message[bytes];
  
  memcpy(
    message, 
    &manifest.pub_signature_key, 
    sizeof(manifest.pub_signature_key)
  );
  memcpy(
    message + sizeof(manifest.pub_signature_key), 
    &manifest.image_length, 
    sizeof(manifest.image_length)
  );
  memcpy(
    message + sizeof(manifest.pub_signature_key) + sizeof(manifest.image_length), 
    manifest.image_code, 
    manifest.image_length
  );   

  char* hash = HASH(message, bytes);

  __CPROVER_assert(__CPROVER_OBJECT_SIZE(hash)==256/8, 
  "PROPERTY 3: Hash is 256 bits");   

  __CPROVER_assert(__CPROVER_r_ok(hash, 256/8),
  "PROPERTY 3: hash is in readable address");  

  //Otherwise OBJECT_SIZE returns size of manifest and not signature.
  signature_t signature = manifest.signature;

  return RSA_VERIFY(rom_ext_pub_key, hash, signature); //0 or 1
}
