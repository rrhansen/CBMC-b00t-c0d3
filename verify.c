#include "verify.h"
#include "mask_rom.h"
#include "RSASSA-PKCS1-V1_5-VERIFY.h"

rom_ext_manifest_t __current_rom_ext_mf;


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

  //Otherwise OBJECT_SIZE returns size of manifest and not signature.
  signature_t signature = manifest.signature;

  int result = RSASSA_PKCS1_V1_5_VERIFY(rom_ext_pub_key.exponent, rom_ext_pub_key.modulus, message, bytes, signature.value, RSA_SIZE, __current_rom_ext_mf);

  return result; //0 or 1
}
