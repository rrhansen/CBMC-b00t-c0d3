#include <string.h>
#include <stdint.h>
#include <malloc.h>
#include <stdlib.h>

#define __REACHABILITY_CHECK __CPROVER_assert(0, "Reachability check, should always \033[0;31mFAIL\033[0m");
#define MAX_ROM_EXTS 5
#define RSA_SIZE 96

//Represents a signature. Needed for CBMC OBJECT_SIZE to see if signature is of ok size
typedef struct signature_t{
    int32_t value[RSA_SIZE];
    //something else
} signature_t;


//Represents a public key
typedef struct pub_key_t{
    int32_t value[RSA_SIZE];
    //something else
} pub_key_t;


//Struct representing rom_ext_manifest
typedef struct rom_ext_manifest_t{
    uint32_t identifier;
      
    signature_t signature;
    
    //public part of signature key
    pub_key_t pub_signature_key;
    uint32_t image_length;
    char* image_code;
} rom_ext_manifest_t;


//Returned by rom_ext_manifests_to_try
typedef struct rom_exts_manifests_t{
    int size;
    rom_ext_manifest_t rom_exts_mfs[MAX_ROM_EXTS];
} rom_exts_manifests_t;


//Represents boot policy
typedef struct boot_policy_t{
    int identifier;
    
    //which rom_ext_slot to boot
    int rom_ext_slot;
    
    //what to do if all ROM Ext are invalid
    void (*fail) ();    

    //what to do if the ROM Ext unexpectedly returns
    void (*fail_rom_ext_terminated) (rom_ext_manifest_t);    

} boot_policy_t;