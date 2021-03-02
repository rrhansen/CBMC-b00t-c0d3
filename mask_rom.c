/*
CBMC Verification of OpenTitan bootcode,
written based on:
sw/device/rom_ext/docs/manifest.md
sw/device/mask_rom/mask_rom.c
sw/device/mask_rom/docs/index.md
doc/security/specs/secure_boot/index.md

*/
#include <string.h>
#include <stdint.h>
#include <malloc.h>


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
    
    //address of entry point
    //note: not part of the doc on the rom_ext_manifest, but included based on code seen in mask_rom.c
    int* entry_point;
    
    signature_t signature;
    
    //public part of signature key
    pub_key_t pub_signature_key;
    char image_code[];
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



typedef void(rom_ext_boot_func)(void); // Function type used to define function pointer to the entry of the ROM_EXT stage.


extern int* READ_FLASH(int start, int end){
    return malloc(end - start); //for CBMC to model reading
};

boot_policy_t read_boot_policy()
{
    int* data = READ_FLASH(0, sizeof(boot_policy_t)); 

    boot_policy_t boot_policy;

    memcpy(&boot_policy.identifier, data, sizeof(boot_policy.identifier));
    memcpy(&boot_policy.rom_ext_slot, data + 1, sizeof(boot_policy.rom_ext_slot));
    memcpy(&boot_policy.fail, data + 2, sizeof(boot_policy.fail));

    return boot_policy;
}


rom_exts_manifests_t rom_ext_manifests_to_try(boot_policy_t boot_policy) {}


pub_key_t read_pub_key(rom_ext_manifest_t current_rom_ext_manifest) {
    return current_rom_ext_manifest.pub_signature_key;
}

extern int CHECK_PUB_KEY_VALID(pub_key_t rom_ext_pub_key) //assumed behavior behavior of check func
{
    for(int i = 0; i < RSA_SIZE; i++){
      if(rom_ext_pub_key.value[i] != 0)
        return 1; // If the key[i] != 0 for one i, the key is valid.
    }
    return 0; // returns a boolean value
} 

extern char* HASH(char* message);

extern int RSA_VERIFY(pub_key_t pub_key, char* message, int32_t* signature);

int verify_rom_ext_signature(pub_key_t rom_ext_pub_key, rom_ext_manifest_t manifest) {
    return RSA_VERIFY(rom_ext_pub_key, HASH(manifest.image_code), manifest.signature.value); //0 or 1
}

extern void WRITE_PMP_REGION(uint8_t reg, uint8_t r, uint8_t w, uint8_t e, uint8_t l);

void pmp_unlock_rom_ext() {
    //Read, Execute, Locked the address space of the ROM extension image
    WRITE_PMP_REGION(       0,          1,          0,          1,          1);
    //                  Region        Read       Write     Execute     Locked 
}

void __some_func(){} //used for CBMC assume

int final_jump_to_rom_ext(rom_ext_manifest_t current_rom_ext_manifest) { // Returns a boolean value.
    __CPROVER_assume(current_rom_ext_manifest.entry_point == &__some_func); //otherwise pointer errors
    
    //Execute rom ext code step 2.iii.e
    rom_ext_boot_func* rom_ext_entry = (rom_ext_boot_func*)current_rom_ext_manifest.entry_point;

    rom_ext_entry();

    //if rom_ext returns, we should return false 
    //and execute step 2.iv.
    return 0;
}

void boot_failed(boot_policy_t boot_policy) {
    boot_policy.fail();
}

void boot_failed_rom_ext_terminated(boot_policy_t boot_policy, rom_ext_manifest_t current_rom_ext_manifest) {
    boot_policy.fail_rom_ext_terminated(current_rom_ext_manifest);
}

int check_rom_ext_manifest(rom_ext_manifest_t manifest) {
    for(int i = 0; i < RSA_SIZE; i++){
      if(manifest.signature.value[i] != 0)
        return 1; // If the signature[i] != 0 for one i, the manifest is valid.
    }
    return 0; 
}

void __func_fail(){} //used for CBMC assume
void __func_fail_rom_ext(rom_ext_manifest_t _){} //used for CBMC assume
int __validated_rom_exts[MAX_ROM_EXTS] = {0,0,0,0,0}; //used for CBMC postcondition

int __help_sign_valid(int* sign){ //used for CBMC assertion + postcondition
    for(int i = 0; i < RSA_SIZE; i++){
      if(sign[i] != 0)
        return 1;
    }
    return 0;
}

int __help_key_valid(int* key){ //used for CBMC assertion + postcondition
    for(int i = 0; i < RSA_SIZE; i++){
      if(key[i] != 0)
        return 1;
    }
    return 0;
}

/*PROPERTY 1 and 2*/
void PROOF_HARNESS(){
    boot_policy_t boot_policy;// = read_boot_policy();
    rom_exts_manifests_t rom_exts_to_try;// = rom_ext_manifests_to_try(boot_policy);

    __CPROVER_assume(rom_exts_to_try.size <= MAX_ROM_EXTS && rom_exts_to_try.size > 0);
    __CPROVER_assume(boot_policy.fail == &__func_fail);
    __CPROVER_assume(boot_policy.fail_rom_ext_terminated == &__func_fail_rom_ext);
    
    mask_rom_boot(boot_policy, rom_exts_to_try);
    
    for(int i = 0; i < rom_exts_to_try.size; i++){
        if(__validated_rom_exts[i]){
            __CPROVER_postcondition(0, "Reachability check, should always \033[0;31mFAIL\033[0m");
            __CPROVER_postcondition(__help_sign_valid(rom_exts_to_try.rom_exts_mfs[i].signature.value), "Postcondition PROPERTY: 1 rom_ext succesfull validation => valid signature");
            __CPROVER_postcondition(__help_key_valid(rom_exts_to_try.rom_exts_mfs[i].pub_signature_key.value), "Postcondition PROPERTY 2: rom_ext succesfull validation => valid key");
        }

    }
    __CPROVER_postcondition(0, "Reachability check, should always \033[0;31mFAIL\033[0m");
}

/*Run Command: 
cbmc mask_rom.c --function PROOF_HARNESS --unwind 100  --unwindset mask_rom_boot.0:6 --unwindset PROOF_HARNESS.0:6 --unwinding-assertions --pointer-check --bounds-check
*/

void mask_rom_boot(boot_policy_t boot_policy, rom_exts_manifests_t rom_exts_to_try ){
    __CPROVER_precondition(rom_exts_to_try.size <= MAX_ROM_EXTS && rom_exts_to_try.size > 0, "Precondition: assumes MAX_ROM_EXTS >= rom_exts > 0");
    __CPROVER_precondition(boot_policy.fail == &__func_fail, "Precondition: assumes boot_policy.fail has ok address");
    __CPROVER_precondition(boot_policy.fail_rom_ext_terminated == &__func_fail_rom_ext, "Precondition: boot_policy.fail_rom_ext_terminated has ok address");

    //Måske step 2.iii
    for (int i = 0; i < rom_exts_to_try.size; i++)
    {
        rom_ext_manifest_t current_rom_ext_manifest = rom_exts_to_try.rom_exts_mfs[i];

        signature_t signature = current_rom_ext_manifest.signature; //needed for __CPROVER_OBJECT_SIZE
        __CPROVER_assert(__CPROVER_OBJECT_SIZE(signature.value) * 8 == 3072, "PROPERTY 1: Signature is 3072-bits");
        
        if (!check_rom_ext_manifest(current_rom_ext_manifest)) {
          __CPROVER_assert(0, "Reachability check, should always \033[0;31mFAIL\033[0m");
          __CPROVER_assert(!__help_sign_valid(current_rom_ext_manifest.signature.value), "PROPERTY 1: Stop verification iff signature is invalid");
          continue;
        }
        __CPROVER_postcondition(0, "Reachability check, should always \033[0;31mFAIL\033[0m");
        __CPROVER_assert(__help_sign_valid(current_rom_ext_manifest.signature.value), "PROPERTY 1: Continue verification iff signature is valid");

        //Step 2.iii.b
        pub_key_t rom_ext_pub_key = read_pub_key(current_rom_ext_manifest); 
        
        __CPROVER_assert(__CPROVER_OBJECT_SIZE(rom_ext_pub_key.value) * 8 == 3072, "PROPERTY 2: Public key is 3072-bits");

        //Step 2.iii.b
        if (!CHECK_PUB_KEY_VALID(rom_ext_pub_key)) {
          __CPROVER_assert(0, "Reachability check, should always \033[0;31mFAIL\033[0m");
          __CPROVER_assert(!__help_key_valid(rom_ext_pub_key.value), "PROPERTY 2: Stop verification iff key is invalid");
            continue;
        }
        __CPROVER_postcondition(0, "Reachability check, should always \033[0;31mFAIL\033[0m");
        __CPROVER_assert(__help_key_valid(rom_ext_pub_key.value), "PROPERTY 2: Continue verification iff key is valid");

       
        //Step 2.iii.b
        if (!verify_rom_ext_signature(rom_ext_pub_key, current_rom_ext_manifest)) {
            continue;
        }
        
        //Step 2.iii.d
        pmp_unlock_rom_ext();
        
        //Step 2.iii.e
        __validated_rom_exts[i] = 1;
        if (!final_jump_to_rom_ext(current_rom_ext_manifest)) {
            //Step 2.iv            
            boot_failed_rom_ext_terminated(boot_policy, current_rom_ext_manifest);
            int n;
            switch(n){ //nondeterministic model the boot_failed_rom_ext_terminated possible behavior
              case 0:
                return;
              default:
                break;
            }
        }
    } // End for

    //Step 2.iv
    boot_failed(boot_policy);
}

