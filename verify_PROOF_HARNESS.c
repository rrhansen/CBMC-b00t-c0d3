#include "verify.h"
#include "mask_rom.h"

void PROOF_HARNESS_VERIFY(){
  rom_ext_manifest_t rom_ext;

  __CPROVER_assume(MAX_IMAGE_LENGTH >  rom_ext.image_length && rom_ext.image_length > 0);
  rom_ext.image_code = malloc(sizeof(char) * rom_ext.image_length );

  if(!verify_rom_ext_signature(rom_ext.pub_signature_key, rom_ext)){
    __REACHABILITY_CHECK
  }
  __REACHABILITY_CHECK
}


/*
PROPERTY 3, 4 ,5

RSA_SIZE = 5
Run: cbmc verify_PROOF_HARNESS.c verify.c sha2-256.c --function PROOF_HARNESS_VERIFY --unwind 11 --unwindset memcmp.0:25 --unwindset sha256_update.0:40 --unwindset sha256_final.0:56 --unwindset sha256_final.1:64 --unwindset sha256_transform.0:17 --unwindset sha256_transform.1:64 --unwindset sha256_transform.2:65 --unwinding-assertions --pointer-check --bounds-check

RSA_SIZE = 96
Run: cbmc verify_PROOF_HARNESS.c verify.c sha2-256.c --function PROOF_HARNESS_VERIFY --unwind 11 --unwindset memcmp.0:403 --unwindset sha256_update.0:403 --unwindset sha256_final.0:56 --unwindset sha256_final.1:64 --unwindset sha256_transform.0:17 --unwindset sha256_transform.1:64 --unwindset sha256_transform.2:65 --unwinding-assertions --pointer-check --bounds-check

*/