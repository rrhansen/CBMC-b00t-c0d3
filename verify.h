#ifndef VERIFY_H
#define VERIFY_H

#include "mask_rom.h"

int verify_rom_ext_signature(pub_key_t rom_ext_pub_key, rom_ext_manifest_t manifest);

#endif