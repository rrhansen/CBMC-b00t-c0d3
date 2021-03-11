#include "mask_rom.h"
#include "PROPERTY3.h"

void PROOF_HARNESS_PROP3(){
  rom_ext_manifest_t rom_ext;

  __CPROVER_assume(10 > rom_ext.image_length && rom_ext.image_length > 0);
  __CPROVER_assume(rom_ext.image_code == malloc(sizeof(char) * rom_ext.image_length));

  verify_rom_ext_signature(rom_ext.pub_signature_key, rom_ext);

  __REACHABILITY_CHECK
}

/*
PROPERTY 3:
cbmc mask_rom.c sha2-256.c PROPERTY3.c --function PROOF_HARNESS_PROP3 --unwind 100 --unwindset sha256_update.0:400 --unwindset mask_rom_boot.0:6 --unwindset PROOF_HARNESS.0:6 --unwinding-assertions --pointer-check --bounds-check

__LIBRARY_MODE 1
__SIMPLE_HASH  0
__SIMPLE_RSA   1

*/