#ifndef VERIFY_H
#define VERIFY_H

#include "mask_rom.h"

extern char* HASH(char* message, int size);
int verify_rom_ext_signature(pub_key_t rom_ext_pub_key, rom_ext_manifest_t manifest);
extern int RSA_VERIFY(pub_key_t pub_key, char* message, int32_t* signature);

#endif