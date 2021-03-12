/*
CBMC Verification of OpenTitan bootcode,
written based on:
sw/device/rom_ext/docs/manifest.md
sw/device/mask_rom/mask_rom.c
sw/device/mask_rom/docs/index.md
doc/security/specs/secure_boot/index.md

*/
#include "sha2-256.h"
#include "mask_rom.h"

#define __LIBRARY_MODE    0 //Used when verifying PROPERTY 3
#define __SIMPLE_HASH     0 //if 1 -> should be verified without sha file
#define __SIMPLE_RSA      1


//for CBMC
int __current_rom_ext = 0;
rom_ext_manifest_t __current_rom_ext_mf;
int __boot_policy_stop = 0;
int __rom_ext_called[MAX_ROM_EXTS] = { }; //used for CBMC postcondition
int __rom_ext_fail_func[MAX_ROM_EXTS] = { }; //for CBMC PROPERTY 6
int __boot_failed_called[MAX_ROM_EXTS] = { };
int __validated_rom_exts[MAX_ROM_EXTS] = { }; //used for CBMC postcondition
int __rom_ext_returned[MAX_ROM_EXTS] = { }; //used for CBMC postcondition
int __imply(int a, int b) { return a ? b : 1; }


//The configured PMP regions for each rom ext.
__PMP_regions_t __rom_ext_pmp_region[MAX_ROM_EXTS];


typedef void(rom_ext_boot_func)(void); // Function type used to define function pointer to the entry of the ROM_EXT stage.


extern int* READ_FLASH(int start, int end) {
    return malloc(end - start); //for CBMC to model reading
};


boot_policy_t read_boot_policy(){
#if !__LIBRARY_MODE
    int* data = READ_FLASH(0, sizeof(boot_policy_t));

    boot_policy_t boot_policy;

    memcpy(&boot_policy.identifier, data, sizeof(boot_policy.identifier));
    memcpy(&boot_policy.rom_ext_slot, data + 1, sizeof(boot_policy.rom_ext_slot));
    memcpy(&boot_policy.fail, data + 2, sizeof(boot_policy.fail));

    return boot_policy;
#endif
}


rom_exts_manifests_t rom_ext_manifests_to_try(boot_policy_t boot_policy) {}


pub_key_t read_pub_key(rom_ext_manifest_t __current_rom_ext_manifest) {
    return __current_rom_ext_manifest.pub_signature_key;
}


extern int CHECK_PUB_KEY_VALID(pub_key_t rom_ext_pub_key){ //assumed behavior behavior of check func
#if !__LIBRARY_MODE    
    if (rom_ext_pub_key.exponent == 0)
        return 0;

    for (int i = 0; i < RSA_SIZE; i++) {
        if (rom_ext_pub_key.modulus[i] != 0)
            return 1; // If the key[i] != 0 for one i, the key is valid.
    }
    return 0; // returns a boolean value
#endif
}


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

#if !__SIMPLE_HASH
  hash = sha256(message, size);
  
  __CPROVER_assert(__CPROVER_r_ok(hash, 256/8),
  "PROPERTY 3: hash is in readable address");

#endif
  
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

#if !__SIMPLE_HASH
    __CPROVER_assert(__CPROVER_OBJECT_SIZE(hash)==256/8, 
    "PROPERTY 3: Hash is 256 bits");    
#endif

    //Otherwise OBJECT_SIZE returns size of manifest and not signature.
    signature_t signature = manifest.signature;

    return RSA_VERIFY(rom_ext_pub_key, hash, signature); //0 or 1
}


extern void WRITE_PMP_REGION(uint8_t reg, uint8_t r, uint8_t w, uint8_t e, uint8_t l);


void pmp_unlock_rom_ext() {
#if !__LIBRARY_MODE
    //Read, Execute, Locked the address space of the ROM extension image
    WRITE_PMP_REGION(       0,           1,          0,          1,         1);
    //                  Region        Read       Write     Execute     Locked 
    __register_pmp_region(__current_rom_ext, 0, 1, 0, 1, 1);
    __REACHABILITY_CHECK
#endif
}


void enable_memory_protection() {
#if !__LIBRARY_MODE
    //Apply PMP region 15 to cover entire flash
    WRITE_PMP_REGION(       15,          1,          0,          0,         1);
    //                  Region        Read       Write     Execute     Locked 

    __register_pmp_region(-1, 15, 1, 0, 0, 1);
    __REACHABILITY_CHECK
#endif
}


void __register_pmp_region(int rom_ext, int pmp_id, int r, int w, int e, int l){
#if !__LIBRARY_MODE
    if (rom_ext == -1) {
        //register PMP region for all rom exts.
        for (int i = 0; i < MAX_ROM_EXTS; i++) {
            __rom_ext_pmp_region[i].pmp_regions[pmp_id].identifier = pmp_id;
            __rom_ext_pmp_region[i].pmp_regions[pmp_id].R = r;
            __rom_ext_pmp_region[i].pmp_regions[pmp_id].W = w;
            __rom_ext_pmp_region[i].pmp_regions[pmp_id].E = e;
            __rom_ext_pmp_region[i].pmp_regions[pmp_id].L = l;
        }
    }
    else {
        __rom_ext_pmp_region[rom_ext].pmp_regions[pmp_id].identifier = pmp_id;
        __rom_ext_pmp_region[rom_ext].pmp_regions[pmp_id].R = r;
        __rom_ext_pmp_region[rom_ext].pmp_regions[pmp_id].W = w;
        __rom_ext_pmp_region[rom_ext].pmp_regions[pmp_id].E = e;
        __rom_ext_pmp_region[rom_ext].pmp_regions[pmp_id].L = l;
    }
#endif
}


void __some_entry_func() { __rom_ext_called[__current_rom_ext] = 1; /*for CBMC PROPERTY 6*/ }


int final_jump_to_rom_ext(rom_ext_manifest_t __current_rom_ext_manifest) { // Returns a boolean value.
#if !__LIBRARY_MODE
    __current_rom_ext_manifest.image_code = &__some_entry_func; //for cbmc
    
    //Execute rom ext code step 2.iii.e
    rom_ext_boot_func* rom_ext_entry = (rom_ext_boot_func*)__current_rom_ext_manifest.image_code;

    __CPROVER_assert(rom_ext_entry == __current_rom_ext_manifest.image_code,
    "PROPERTY 6: Correct entry point address.");

    __REACHABILITY_CHECK

    rom_ext_entry();

    __rom_ext_returned[__current_rom_ext] = 1; //for CBMC PROPERTY 6

    //if rom_ext returns, we should return false 
    //and execute step 2.iv.
    return 0;
#endif
}


void boot_failed(boot_policy_t boot_policy) {
    boot_policy.fail();
}


void boot_failed_rom_ext_terminated(boot_policy_t boot_policy, rom_ext_manifest_t __current_rom_ext_manifest) {
#if !__LIBRARY_MODE
    __REACHABILITY_CHECK

    boot_policy.fail_rom_ext_terminated(__current_rom_ext_manifest);
#endif
}


int check_rom_ext_manifest(rom_ext_manifest_t manifest) {
#if !__LIBRARY_MODE
    for (int i = 0; i < RSA_SIZE; i++) {
        if (manifest.signature.value[i] != 0)
            return 1; // If the signature[i] != 0 for one i, the manifest is valid.
    }
    return 0;
#endif
}


int __help_sign_valid(signature_t sign) { //used for CBMC assertion + postcondition
#if !__LIBRARY_MODE
    for (int i = 0; i < RSA_SIZE; i++) {
        if (sign.value[i] != 0)
            return 1;
    }
    return 0;
#endif
}


int __help_pkey_valid(pub_key_t pkey) { //used for CBMC assertion + postcondition
#if !__LIBRARY_MODE
    if (pkey.exponent == 0)
        return 0;

    for (int i = 0; i < RSA_SIZE; i++) {
        if (pkey.modulus[i] != 0)
            return 1;
    }
    return 0;
#endif
}


int __help_check_pmp_region(int rom_ext, int pmp_id, int r, int w, int e, int l) {
#if !__LIBRARY_MODE
    if (rom_ext == -1) {
        //When we need to check a PMP region for all rom exts
        for (int i = 0; i < MAX_ROM_EXTS; i++) {
            // If something is wrong return 0
            if (__rom_ext_pmp_region[i].pmp_regions[pmp_id].R != r           ||
                __rom_ext_pmp_region[i].pmp_regions[pmp_id].W != w           ||
                __rom_ext_pmp_region[i].pmp_regions[pmp_id].E != e           ||
                __rom_ext_pmp_region[i].pmp_regions[pmp_id].L != l)
                return 0;
        }
        return 1;
    }
    else {
        return __rom_ext_pmp_region[rom_ext].pmp_regions[pmp_id].R == r &&
            __rom_ext_pmp_region[rom_ext].pmp_regions[pmp_id].W == w &&
            __rom_ext_pmp_region[rom_ext].pmp_regions[pmp_id].E == e &&
            __rom_ext_pmp_region[rom_ext].pmp_regions[pmp_id].L == l;
    }
#endif
}


int __help_all_pmp_inactive(){
#if !__LIBRARY_MODE
    //Inactive if all fields are 0.
    for (int i = 0; i < MAX_ROM_EXTS; i++) {
        for (int j = 0; j < PMP_REGIONS; j++) {
            if (__rom_ext_pmp_region[i].pmp_regions[j].R != 0 ||
                __rom_ext_pmp_region[i].pmp_regions[j].W != 0 ||
                __rom_ext_pmp_region[i].pmp_regions[j].E != 0 ||
                __rom_ext_pmp_region[i].pmp_regions[j].L != 0)
                return 0;
        }
    }
    return 1;
#endif
}


void __func_fail() { __boot_failed_called[__current_rom_ext] = 1; } //used for CBMC
void __func_fail_rom_ext(rom_ext_manifest_t _) { __rom_ext_fail_func[__current_rom_ext] = 1; } //used for CBMC


void PROOF_HARNESS() {
#if !__LIBRARY_MODE
    boot_policy_t boot_policy = read_boot_policy();
    rom_exts_manifests_t rom_exts_to_try = rom_ext_manifests_to_try(boot_policy);

    __CPROVER_assume(rom_exts_to_try.size <= MAX_ROM_EXTS && rom_exts_to_try.size > 0);
    __CPROVER_assume(boot_policy.fail == &__func_fail);
    __CPROVER_assume(boot_policy.fail_rom_ext_terminated == &__func_fail_rom_ext);
    
    for(int i = 0; i < rom_exts_to_try.size; i++){
      __CPROVER_assume(10 >  rom_exts_to_try.rom_exts_mfs[i].image_length && rom_exts_to_try.rom_exts_mfs[i].image_length > 0);
      rom_exts_to_try.rom_exts_mfs[i].image_code = malloc(sizeof(char) *rom_exts_to_try.rom_exts_mfs[i].image_length );
    }

    mask_rom_boot(boot_policy, rom_exts_to_try);


    __CPROVER_postcondition(__current_rom_ext + 1 <= rom_exts_to_try.size,
    "Postcondition: Should never check more rom_ext than there exist");

    for (int i = 0; i < rom_exts_to_try.size; i++) {
        if (__validated_rom_exts[i]) { //validated - try to boot from
            __REACHABILITY_CHECK

            __CPROVER_postcondition(__help_sign_valid(rom_exts_to_try.rom_exts_mfs[i].signature),
            "Postcondition PROPERTY 1: rom_ext VALIDATED => valid signature");

            __CPROVER_postcondition(__help_pkey_valid(rom_exts_to_try.rom_exts_mfs[i].pub_signature_key),
            "Postcondition PROPERTY 2: rom_ext VALIDATED => valid key");

            __CPROVER_postcondition(__rom_ext_called[i],
            "Postcondition PROPERTY 6: rom_ext VALIDATED => rom ext code inititated");

            __CPROVER_postcondition(__imply(__rom_ext_returned[i], __rom_ext_fail_func[i]),
            "Postcondition PROPERTY 6: (valid rom _ext and rom_ext code return) => that rom_ext term func is called");

            __CPROVER_postcondition(__imply(!__rom_ext_returned[i], !__rom_ext_fail_func[i]),
            "Postcondition PROPERTY 6: (valid rom _ext and rom_ext code !return) => that rom_ext term func not called");

            __CPROVER_assert(__help_check_pmp_region(i, 15, 1, 0, 0, 1),
            "Postcondition PROPERTY 9: PMP region 15 should be R and L, when rom_ext was validated.");

            __CPROVER_assert(__help_check_pmp_region(i, 0, 1, 0, 1, 1),
            "Postcondition PROPERTY 10: If rom_ext was valided, then PMP region 0 should be R, E, and L.");
            
        }
        else { //invalidated - unsafe to boot from
            __REACHABILITY_CHECK

            __CPROVER_postcondition(__imply(!__rom_ext_returned[i], !__rom_ext_fail_func[i]),
            "Postcondition PROPERTY 6: (invalid rom _ext and rom_ext code !return) => that rom_ext term func not called");

            __CPROVER_postcondition(!__rom_ext_called[i],
            "Postcondition PROPERTY 7: rom_ext INVALIDATED => rom ext code not executed");

            __CPROVER_postcondition(__current_rom_ext > i || (i + 1) == rom_exts_to_try.size || __boot_policy_stop,
            "Postcondition PROPERTY 7: rom_ext INVALIDATED => we check the next rom_ext if any left and no boot policy instructed stop");

            __CPROVER_postcondition(__imply(i < __current_rom_ext, !__boot_failed_called[i]),
            "Postcondition PROPERTY 8: A rom_ext (not the last one) fails => fail func is not called");

            __CPROVER_postcondition(__imply(i == __current_rom_ext, __boot_failed_called[i]),
            "Postcondition PROPERTY 8: Last rom_ext fail => fail func has been called");

            __CPROVER_assert(__help_check_pmp_region(i, 15, 1, 0, 0, 1),
            "Postcondition PROPERTY 9: PMP region 15 should be R and L. Even if rom_ext was invalidated.");

            __CPROVER_assert(__help_check_pmp_region(i, 0, 0, 0, 0, 0),
            "Postcondition PROPERTY 10: If rom_ext was invalid, PMP region 0 should not be R, E, W, and L.");
        }

    }
    __REACHABILITY_CHECK
#endif
}

/*
PROPERTY 1, 2, 4, 6, 7, 8, 9, 10

__LIBRARY_MODE 0
__SIMPLE_HASH  1
__SIMPLE_RSA   1

Run Command.
cbmc mask_rom.c --function PROOF_HARNESS --unwind 100 --unwindset memcmp.0:400 --unwindset mask_rom_boot.0:6 --unwindset PROOF_HARNESS.0:6 --unwinding-assertions --pointer-check --bounds-check
*/


void mask_rom_boot(boot_policy_t boot_policy, rom_exts_manifests_t rom_exts_to_try ){
#if !__LIBRARY_MODE
    __CPROVER_precondition(rom_exts_to_try.size <= MAX_ROM_EXTS && rom_exts_to_try.size > 0, 
    "Precondition: Assumes MAX_ROM_EXTS >= rom_exts > 0");

    __CPROVER_precondition(boot_policy.fail == &__func_fail,
    "Precondition: Assumes boot_policy.fail has ok address");

    __CPROVER_precondition(boot_policy.fail_rom_ext_terminated == &__func_fail_rom_ext,
    "Precondition: Assumes boot_policy.fail_rom_ext_terminated has ok address");

    //All pmp regions should be inactive at this point
    __CPROVER_precondition(__help_all_pmp_inactive(),
    "Precondition PROPERTY 9: All PMP regions should be unset at beginning of mask_rom.");

    enable_memory_protection();   

    //Måske step 2.iii
    for (int i = 0; i < rom_exts_to_try.size; i++) {

        __CPROVER_assert(__help_check_pmp_region(i, 15, 1, 0, 0, 1),
        "PROPERTY 9: PMP region 15 should be R and L.");

        __current_rom_ext = i;
        rom_ext_manifest_t __current_rom_ext_manifest = rom_exts_to_try.rom_exts_mfs[i];

        signature_t signature = __current_rom_ext_manifest.signature; //needed for __CPROVER_OBJECT_SIZE

        __CPROVER_assert(__CPROVER_OBJECT_SIZE(signature.value) * 8 == RSA_SIZE*32,
        "PROPERTY 1: Signature is 3072-bits");

        if (!check_rom_ext_manifest(__current_rom_ext_manifest)) {
            __REACHABILITY_CHECK

            __CPROVER_assert(!__help_sign_valid(__current_rom_ext_manifest.signature),
            "PROPERTY 1: Stop verification iff signature is invalid");

            continue;
        }

        __REACHABILITY_CHECK

        __CPROVER_assert(__help_sign_valid(__current_rom_ext_manifest.signature),
        "PROPERTY 1: Continue verification iff signature is valid");

        //Step 2.iii.b
        pub_key_t rom_ext_pub_key = read_pub_key(__current_rom_ext_manifest);

        __CPROVER_assert(__CPROVER_OBJECT_SIZE(rom_ext_pub_key.modulus) * 8 == RSA_SIZE*32+32,
        "PROPERTY 2: Public key modulus is 3072-bits and exponent is 32 bits.");

        //Step 2.iii.b
        if (!CHECK_PUB_KEY_VALID(rom_ext_pub_key)) {
            __REACHABILITY_CHECK

            __CPROVER_assert(!__help_pkey_valid(rom_ext_pub_key),
            "PROPERTY 2: Stop verification iff key is invalid");

            continue;
        }

        __REACHABILITY_CHECK

        __CPROVER_assert(__help_pkey_valid(rom_ext_pub_key),
        "PROPERTY 2: Continue verification iff key is valid");

        //Step 2.iii.b
        if (!verify_rom_ext_signature(rom_ext_pub_key, __current_rom_ext_manifest)) {
            __REACHABILITY_CHECK
            continue;
        }
        __REACHABILITY_CHECK
        __validated_rom_exts[i] = 1; //for CBMC

        //Step 2.iii.d
        pmp_unlock_rom_ext();
                
        __CPROVER_assert(__help_check_pmp_region(i, 0, 1, 0, 1, 1),
        "PROPERTY 10: PMP region 0 should be R, E, and L.");

        //Step 2.iii.e
        if (!final_jump_to_rom_ext(__current_rom_ext_manifest)) {
            __REACHABILITY_CHECK

            //Step 2.iv            
            boot_failed_rom_ext_terminated(boot_policy, __current_rom_ext_manifest);
            __boot_policy_stop = 1;
            return;
        }
    } // End for

    __REACHABILITY_CHECK

    //Step 2.iv
    boot_failed(boot_policy);
#endif
}



/*
//It works with the following configuration and command. It checks for all properties.: 
#define __LIBRARY_MODE    0 //Used when verifying PROPERTY 3
#define __SIMPLE_HASH     0 //if 1 -> should be verified without sha file
#define __SIMPLE_RSA      1

#define MAX_ROM_EXTS 1
#define RSA_SIZE 5
#define PMP_REGIONS 16

cbmc mask_rom.c sha2-256.c --function PROOF_HARNESS --unwind 100 --unwindset memcmp.0:25 --unwindset mask_rom_boot.0:6 --unwindset PROOF_HARNESS.0:6 --unwinding-assertions --pointer-check --bounds-check

Result should be: 18 out of 778 failed.

--unwindset memcmp.0:25 is due to memcmp in HASH.

*/




