/*
CBMC Verification of OpenTitan bootcode,
written based on:
sw/device/rom_ext/docs/manifest.md
sw/device/mask_rom/mask_rom.c
sw/device/mask_rom/docs/index.md
doc/security/specs/secure_boot/index.md

*/
#include "hmac.h"
#include "mask_rom.h"
#include "memory_compare.h"

//HMAC key in OTP/Keymanager
BYTE __hmac_key[HMAC_KEY_SIZE];

//Whitelist in ROM
#define __PKEY_WHITELIST_SIZE 1
pub_key_t __pkey_whitelist[__PKEY_WHITELIST_SIZE];

//for CBMC
int __current_rom_ext = 0;
rom_ext_manifest_t __current_rom_ext_mf;
int __boot_policy_stop = 0;
int __rom_ext_called[MAX_ROM_EXTS] = { }; //used for CBMC postcondition
int __rom_ext_fail_func[MAX_ROM_EXTS] = { }; //for CBMC PROPERTY 6
int __boot_failed_called[MAX_ROM_EXTS] = { };
int __validated_rom_exts[MAX_ROM_EXTS] = { }; //used for CBMC postcondition
int __rom_ext_returned[MAX_ROM_EXTS] = { }; //used for CBMC postcondition
int __verify_signature_called[MAX_ROM_EXTS] = { };
int __imply(int a, int b) { return a ? b : 1; }
int __valid_signature[MAX_ROM_EXTS] = { }; //result of verify_rom_ext_signature


//The configured PMP regions for each rom ext.
__PMP_regions_t __rom_ext_pmp_region[MAX_ROM_EXTS];

// Function type used to define function pointer to the entry of the ROM_EXT stage.
typedef void(rom_ext_boot_func)(void); 

// Function type for entry point of boot policy fail function
typedef void(fail_func)(void); 

// Function type for entry point of boot policy fail rom ext terminated function.
typedef void(fail_rom_ext_terminated_func)(rom_ext_manifest_t); 


int verify_rom_ext_signature(pub_key_t rom_ext_pub_key, rom_ext_manifest_t manifest) {
	__CPROVER_precondition(MAX_IMAGE_LENGTH >= manifest.image_length && manifest.image_length > 0,
		"Precondition: Assumes rom ext image code is < 10 and > 0");

	__CPROVER_precondition(__CPROVER_r_ok(manifest.image_code, manifest.image_length),
		"Precondition: Assumes rom ext image code is readable");

	__verify_signature_called[__current_rom_ext] = 1;

	int bytes =
		sizeof(manifest.pub_signature_key) + sizeof(manifest.image_length) + manifest.image_length;

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

	int result = OTBN_RSASSA_PKCS1_V1_5_VERIFY(rom_ext_pub_key.exponent, rom_ext_pub_key.modulus, message, bytes, signature.value, RSA_SIZE, manifest);

	return result; //0 or 1
}


int __is_valid_params(int32_t exponent, int32_t* modulus, char* message, int message_len, int32_t* signature, int signature_len, rom_ext_manifest_t __current_rom_ext_mf) {

	if (exponent != __current_rom_ext_mf.pub_signature_key.exponent)
		return 0;

	if (cmp_modulus(modulus,
		__current_rom_ext_mf.pub_signature_key.modulus,
		RSA_SIZE*sizeof(int32_t)) != 0)
		return 0;

	if (cmp_signature(signature,
		__current_rom_ext_mf.signature.value,
		RSA_SIZE * sizeof(int32_t)) != 0)
		return 0;

	//Message is: pkey+image_length+image_code
	if (cmp_key(message,
		&__current_rom_ext_mf.pub_signature_key,
		sizeof(__current_rom_ext_mf.pub_signature_key)) != 0)
		return 0;

	if (cmp_image_len(
		message + sizeof(__current_rom_ext_mf.pub_signature_key),
		&__current_rom_ext_mf.image_length,
		sizeof(__current_rom_ext_mf.image_length)) != 0)
		return 0;

	if (cmp_image_code(
		message + sizeof(__current_rom_ext_mf.pub_signature_key) + sizeof(__current_rom_ext_mf.image_length),
		__current_rom_ext_mf.image_code,
		__current_rom_ext_mf.image_length) != 0)
		return 0;


	return 1;
}


char* OTBN_RSA_3072_DECRYPT(int32_t* signature, int signature_len, int32_t exponent, int32_t* modulus) {
	char* decrypt = malloc(256 / 8); //model it to be ok for PROPERTY 5
	return decrypt;
}

int OTBN_RSASSA_PKCS1_V1_5_VERIFY(int32_t exponent, int32_t* modulus, char* message, int message_len, int32_t* signature, int signature_len, rom_ext_manifest_t __current_rom_ext_mf) {
	__CPROVER_assert(__CPROVER_OBJECT_SIZE(message) == message_len,
		"PROPERTY 5: Formal parameter message_len lenght matches actual message length.");

	__CPROVER_assert(__CPROVER_OBJECT_SIZE(signature) * 8 == 3072,
		"PROPERTY 5: Signature to be verified is 3072-bits.");

	__CPROVER_assert(__CPROVER_OBJECT_SIZE(signature) == signature_len * sizeof(int32_t),
		"PROPERTY 5: Formal parameter signature lenght matches actual signature length.");

	__CPROVER_assert(sizeof(exponent) * 8 == 32,
		"PROPERTY 5: Public key exponent is 32 bits.");

	__CPROVER_assert((sizeof(pub_key_t) - sizeof(exponent)) * 8 == 3072,
		"PROPERTY 5: Public key modulus is 3072-bits.");

	__CPROVER_assert(__is_valid_params(exponent, modulus, message, message_len, signature,
		signature_len, __current_rom_ext_mf),
		"PROPERTY 5: Check that key, signature, and message matches those from the manifest.");

	__REACHABILITY_CHECK

	if (signature_len != RSA_SIZE) {
		__CPROVER_assert(signature_len * 32 != 3072,
			"PROPERTY 5: Length checking: If the length of the signature is not 3072 bytes, stop.");
		__REACHABILITY_CHECK // Not reachable atm

			return 0;
	}
	__REACHABILITY_CHECK

	char* decrypt = OTBN_RSA_3072_DECRYPT(signature, signature_len, exponent, modulus);
	char* hash = HMAC_SHA2_256(__hmac_key, message, message_len, __current_rom_ext_mf); //message_len in bytes

	__CPROVER_assert(!__CPROVER_array_equal(decrypt, signature),
		"PROPERTY 5: Decrypted signature is different from signature");

	__CPROVER_assert(!__CPROVER_array_equal(hash, message),
		"PROPERTY 5: Hash is different from original message");

	__CPROVER_assert(__CPROVER_OBJECT_SIZE(decrypt) == 256 / 8,
		"PROPERTY 5: Decrypted message is 256 bits");

	__CPROVER_assert(__CPROVER_r_ok(decrypt, 256 / 8),
		"PROPERTY 5: Decrypted message is in readable address");

	__CPROVER_assert(__CPROVER_OBJECT_SIZE(hash) == 256 / 8,
		"PROPERTY 3: Hash is 256 bits");

	__CPROVER_assert(__CPROVER_r_ok(hash, 256 / 8),
		"PROPERTY 3: hash is in readable address");

	if (cmp_hash_decrypt(hash, decrypt, 256 / 8) == 0){
		__valid_signature[__current_rom_ext] = 1;
		return 1; //verified
	}
	else{
		__valid_signature[__current_rom_ext] = 0;
		return 0;
	}
}


boot_policy_t FLASH_CTRL_read_boot_policy() {}


rom_exts_manifests_t FLASH_CTRL_rom_ext_manifests_to_try(boot_policy_t boot_policy) {}


pub_key_t read_pub_key(rom_ext_manifest_t current_rom_ext_manifest) {
	return current_rom_ext_manifest.pub_signature_key;
}

//Mocked function for reading pkey whitelist from maskrom.
pub_key_t* ROM_CTRL_get_whitelist() {
	return __pkey_whitelist;
}


extern int check_pub_key_valid(pub_key_t rom_ext_pub_key){ //assumed behavior behavior of check func
	pub_key_t* pkey_whitelist = ROM_CTRL_get_whitelist();

	for (int i = 0; i < __PKEY_WHITELIST_SIZE; i++) {
		if (pkey_whitelist[i].exponent != rom_ext_pub_key.exponent)
			continue;

		int j = 0;
		for (j = 0; j < RSA_SIZE; j++) {
			if (pkey_whitelist[i].modulus[j] != rom_ext_pub_key.modulus[j])
				break;
		}

		//if j == RSA_SIZE, then loop ran to completion and all entries were equal
		if (j == RSA_SIZE)
			return 1;
	}

	return 0;
}


extern void PMP_WRITE_REGION(uint8_t reg, uint8_t r, uint8_t w, uint8_t e, uint8_t l){
	__REACHABILITY_CHECK
}


void PMP_unlock_rom_ext() {
	//Read, Execute, Locked the address space of the ROM extension image
	PMP_WRITE_REGION(        0,        1,        0,        1,        1);
	//                  Region      Read     Write	  Execute	  Locked 
	__register_pmp_region(__current_rom_ext, 0, 1, 0, 1, 1);
	__REACHABILITY_CHECK
}


void PMP_enable_memory_protection() {
	//Apply PMP region 15 to cover entire flash
	PMP_WRITE_REGION(       15,        1,        0,        0,        1);
	//                  Region      Read     Write   Execute    Locked 

	__register_pmp_region(-1, 15, 1, 0, 0, 1);
	__REACHABILITY_CHECK
}


void __register_pmp_region(int rom_ext, int pmp_id, int r, int w, int e, int l){
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
}


void __some_entry_func() { __rom_ext_called[__current_rom_ext] = 1; /*for CBMC PROPERTY 6*/ }


int final_jump_to_rom_ext(rom_ext_manifest_t current_rom_ext_manifest) { // Returns a boolean value.
	//This assumption causes reachability checks to succeed. If == is =, then they fail.
	//__CPROVER_assume(current_rom_ext_manifest.image_code == &__some_entry_func); //for cbmc
	current_rom_ext_manifest.image_code = &__some_entry_func;
	//Execute rom ext code step 2.iii.e
	rom_ext_boot_func* rom_ext_entry = (rom_ext_boot_func*)current_rom_ext_manifest.image_code;

	__CPROVER_assert(rom_ext_entry == current_rom_ext_manifest.image_code,
	"PROPERTY 6: Correct entry point address.");

	__REACHABILITY_CHECK

	rom_ext_entry();

	__rom_ext_returned[__current_rom_ext] = 1; //for CBMC PROPERTY 6

	//if rom_ext returns, we should return false 
	//and execute step 2.iv.
	return 0;
}


void boot_failed(boot_policy_t boot_policy) {
	__REACHABILITY_CHECK
	fail_func* fail_func_entry = (fail_func*)boot_policy.fail;
	fail_func_entry();
}


void boot_failed_rom_ext_terminated(boot_policy_t boot_policy, rom_ext_manifest_t current_rom_ext_manifest) {
	__REACHABILITY_CHECK
	fail_rom_ext_terminated_func* fail_func_entry = (fail_rom_ext_terminated_func*)boot_policy.fail_rom_ext_terminated;
	fail_func_entry(current_rom_ext_manifest);
}


int check_rom_ext_manifest(rom_ext_manifest_t manifest) {
	if (manifest.identifier == 0)
		return 0;
	for (int i = 0; i < RSA_SIZE; i++) {
		if (manifest.signature.value[i] != 0)
			return 1; // If the signature[i] != 0 for one i, the manifest is valid.
	}
	return 0;
}


int __help_check_rom_ext_manifest(rom_ext_manifest_t manifest) { //used for CBMC assertion + postcondition
	if (manifest.identifier == 0)
		return 0;
	
	if (__CPROVER_OBJECT_SIZE(manifest.signature.value) * 8 != 3072) //Signature must be 3072 bits
		return 0;

	for (int i = 0; i < RSA_SIZE; i++) {
		if (manifest.signature.value[i] != 0)
			return 1;
	}
	return 0;
}


int __help_pkey_valid(pub_key_t pkey) { //used for CBMC assertion + postcondition
	// Public key exponent must be 32 bits.");
	if(sizeof(pkey.exponent) * 8 != 32)
		return 0;
	// Public key modulus must be 3072-bits.");
	if((sizeof(pkey) - sizeof(pkey.exponent)) * 8 != 3072)
		return 0;

	pub_key_t* pkey_whitelist = ROM_CTRL_get_whitelist();

	for (int i = 0; i < __PKEY_WHITELIST_SIZE; i++) {
		if (pkey_whitelist[i].exponent != pkey.exponent)
			continue;

		int j = 0;
		for (j = 0; j < RSA_SIZE; j++) {
			if (pkey_whitelist[i].modulus[j] != pkey.modulus[j])
				break;
		}

		//if j == RSA_SIZE, then loop ran to completion and all entries were equal
		if (j == RSA_SIZE)
			return 1;
	}

	return 0;
}


int __help_check_pmp_region(int rom_ext, int pmp_id, int r, int w, int e, int l) {
	if (rom_ext == -1) {
		//When we need to check a PMP region for all rom exts
		for (int i = 0; i < MAX_ROM_EXTS; i++) {
			// If something is wrong return 0
			if (__rom_ext_pmp_region[i].pmp_regions[pmp_id].R != r    ||
				__rom_ext_pmp_region[i].pmp_regions[pmp_id].W != w      ||
				__rom_ext_pmp_region[i].pmp_regions[pmp_id].E != e      ||
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
}


int __help_all_pmp_inactive(){
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
}

void __func_fail() { __boot_failed_called[__current_rom_ext] = 1; } //used for CBMC
void __func_fail_rom_ext(rom_ext_manifest_t _) { __rom_ext_fail_func[__current_rom_ext] = 1; } //used for CBMC

void PROOF_HARNESS() {
	boot_policy_t boot_policy = FLASH_CTRL_read_boot_policy();
	rom_exts_manifests_t rom_exts_to_try = FLASH_CTRL_rom_ext_manifests_to_try(boot_policy);

	__CPROVER_assume(rom_exts_to_try.size <= MAX_ROM_EXTS && rom_exts_to_try.size > 0);

	__CPROVER_assume(boot_policy.fail == &__func_fail);
	__CPROVER_assume(boot_policy.fail_rom_ext_terminated == &__func_fail_rom_ext);

	for(int i = 0; i < rom_exts_to_try.size; i++){
		__CPROVER_assume(MAX_IMAGE_LENGTH >= rom_exts_to_try.rom_exts_mfs[i].image_length && rom_exts_to_try.rom_exts_mfs[i].image_length > 0);
		rom_exts_to_try.rom_exts_mfs[i].image_code = malloc(sizeof(char) * rom_exts_to_try.rom_exts_mfs[i].image_length);
	}

	mask_rom_boot(boot_policy, rom_exts_to_try);


	__CPROVER_postcondition(__current_rom_ext + 1 <= rom_exts_to_try.size,
	"Postcondition: Should never check more rom_ext than there exist");

	for (int i = 0; i < rom_exts_to_try.size; i++) {

		__CPROVER_postcondition(__imply(!__help_check_rom_ext_manifest(rom_exts_to_try.rom_exts_mfs[i]) ||
								!__help_pkey_valid(rom_exts_to_try.rom_exts_mfs[i].pub_signature_key),
								!__verify_signature_called[i]),
		"Postcondition PROPERTY 5: If identifier, sign, or key is invalid then verify signature function is not called");

		__CPROVER_postcondition(__imply(__help_check_rom_ext_manifest(rom_exts_to_try.rom_exts_mfs[i]) &&
								__help_pkey_valid(rom_exts_to_try.rom_exts_mfs[i].pub_signature_key),
								__verify_signature_called[i]),
		"Postcondition PROPERTY 5: If identifier, sign, and key are valid then the signature verification function is called");

		if (__validated_rom_exts[i]) { //validated - try to boot from
			__REACHABILITY_CHECK

			__CPROVER_postcondition(__help_check_rom_ext_manifest(rom_exts_to_try.rom_exts_mfs[i]),
			"Postcondition PROPERTY 1: rom_ext VALIDATED => valid signature");

			__CPROVER_postcondition(__help_pkey_valid(rom_exts_to_try.rom_exts_mfs[i].pub_signature_key),
			"Postcondition PROPERTY 2: rom_ext VALIDATED => valid key");

			__CPROVER_postcondition(__verify_signature_called[i],
			"Postcondition PROPERTY 5: iff manifest is valid then verify signature function is called");

			__CPROVER_postcondition(__valid_signature[i],
			"Postcondition PROPERTY 5: rom_ext VALIDATED => signature valid");

			__CPROVER_postcondition(__rom_ext_called[i],
			"Postcondition PROPERTY 6: rom_ext VALIDATED => rom ext code inititated");

			__CPROVER_postcondition(__imply(__rom_ext_returned[i], __rom_ext_fail_func[i]),
			"Postcondition PROPERTY 6: (valid rom _ext and rom_ext code return) => that rom_ext term func is called");

			__CPROVER_postcondition(__imply(!__rom_ext_returned[i], !__rom_ext_fail_func[i]),
			"Postcondition PROPERTY 6: (valid rom _ext and rom_ext code !return) => that rom_ext term func not called");

			__CPROVER_postcondition(__help_check_pmp_region(i, 15, 1, 0, 0, 1),
			"Postcondition PROPERTY 9: PMP region 15 should be R and L, when rom_ext was validated.");

			__CPROVER_postcondition(__help_check_pmp_region(i, 0, 1, 0, 1, 1),
			"Postcondition PROPERTY 10: If rom_ext was valided, then PMP region 0 should be R, E, and L.");
			
		}
		else { //invalidated - unsafe to boot from
			__REACHABILITY_CHECK

			__CPROVER_postcondition(!__help_check_rom_ext_manifest(rom_exts_to_try.rom_exts_mfs[i]) ||
									!__help_pkey_valid(rom_exts_to_try.rom_exts_mfs[i].pub_signature_key) ||
									!__valid_signature[i],
			"Postcondition: rom_ext INVALIDATED => identifier, signature, or key is invalid");

			__CPROVER_postcondition(!__valid_signature[i],
			"Postcondition PROPERTY 5: rom_ext INVALIDATED => signature invalid or not checked");

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

			__CPROVER_postcondition(__help_check_pmp_region(i, 15, 1, 0, 0, 1),
			"Postcondition PROPERTY 9: PMP region 15 should be R and L. Even if rom_ext was invalidated.");

			__CPROVER_postcondition(__help_check_pmp_region(i, 0, 0, 0, 0, 0),
			"Postcondition PROPERTY 10: If rom_ext was invalid, PMP region 0 should not be R, E, W, and L.");
		}
	}
	__REACHABILITY_CHECK
}

/*
PROPERTY 1, 2, 6, 7, 8, 9, 10

RSA_SIZE = 96
Run:
cbmc mask_rom.c mock_hmac.c memory_compare.c --function PROOF_HARNESS --unwind 97 --unwindset cmp_key.0:390 --unwindset cmp_image_len.0:5 --unwindset cmp_image_code.0:3 --unwindset cmp_modulus.0:385 --unwindset cmp_signature.0:385 --unwindset cmp_has_decrypt.0:33 --unwindset mask_rom_boot.0:2 --unwindset PROOF_HARNESS.0:2 --unwinding-assertions --pointer-check --bounds-check

RSA_SIZE = 5
Run: 
cbmc mask_rom.c mock_hmac.c memory_compare.c --function PROOF_HARNESS --unwind 33 --unwindset memcmp.0:25 --unwindset mask_rom_boot.0:2 --unwindset PROOF_HARNESS.0:2 --unwinding-assertions --pointer-check --bounds-check


PROPERTY 1, 2, 3, 4, 5, 6, 7, 8, 9, 10
RSA_SIZE = 96
Run: (OUTDATED)
cbmc mask_rom.c hmac.c memory_compare.c --function PROOF_HARNESS --unwind 97 --unwindset memcmp.0:400 --unwindset mask_rom_boot.0:6 --unwindset PROOF_HARNESS.0:6  --unwindset memcmp.0:25 --unwindset sha256_update.0:40 --unwindset sha256_final.0:56 --unwindset sha256_final.1:64 --unwindset sha256_transform.0:17 --unwindset sha256_transform.1:64 --unwindset sha256_transform.2:65 --unwinding-assertions --pointer-check --bounds-check

RSA_SIZE = 5
Run: (OUTDATED)
cbmc mask_rom.c hmac.c memory_compare.c --function PROOF_HARNESS --unwind 20 --unwindset memcmp.0:40 --unwindset mask_rom_boot.0:6 --unwindset PROOF_HARNESS.0:6  --unwindset memcmp.0:25 --unwindset sha256_update.0:40 --unwindset sha256_final.0:56 --unwindset sha256_final.1:64 --unwindset sha256_transform.0:17 --unwindset sha256_transform.1:64 --unwindset sha256_transform.2:65 --unwinding-assertions --pointer-check --bounds-check


Result should be: 18 out of 778 failed.

--unwindset memcmp.0:25 is due to memcmp in HASH.
*/


void mask_rom_boot(boot_policy_t boot_policy, rom_exts_manifests_t rom_exts_to_try ){
	__CPROVER_precondition(rom_exts_to_try.size <= MAX_ROM_EXTS && rom_exts_to_try.size > 0, 
	"Precondition: Assumes MAX_ROM_EXTS >= rom_exts > 0");

	__CPROVER_precondition(boot_policy.fail == &__func_fail,
	"Precondition: Assumes boot_policy.fail has ok address");

	__CPROVER_precondition(boot_policy.fail_rom_ext_terminated == &__func_fail_rom_ext,
	"Precondition: Assumes boot_policy.fail_rom_ext_terminated has ok address");

	//All pmp regions should be inactive at this point
	__CPROVER_precondition(__help_all_pmp_inactive(),
	"Precondition PROPERTY 9: All PMP regions should be unset at beginning of mask_rom.");

	PMP_enable_memory_protection();

	//Måske step 2.iii
	for (int i = 0; i < rom_exts_to_try.size; i++) {

		__CPROVER_assert(__help_check_pmp_region(i, 15, 1, 0, 0, 1),
		"PROPERTY 9: PMP region 15 should be R and L.");

		__current_rom_ext = i;
		rom_ext_manifest_t current_rom_ext_manifest = rom_exts_to_try.rom_exts_mfs[i];

		signature_t __signature = current_rom_ext_manifest.signature; //needed for __CPROVER_OBJECT_SIZE


		if (!check_rom_ext_manifest(current_rom_ext_manifest)) {
			__REACHABILITY_CHECK

			__CPROVER_assert(!__help_check_rom_ext_manifest(current_rom_ext_manifest),
			"PROPERTY 1: Stop verification if signature or identifier is invalid");

			continue;
		}

		__REACHABILITY_CHECK

		__CPROVER_assert(__help_check_rom_ext_manifest(current_rom_ext_manifest),
		"PROPERTY 1: Continue verification if signature and identifier are valid");

		//Step 2.iii.b
		pub_key_t rom_ext_pub_key = read_pub_key(current_rom_ext_manifest);	

		//Step 2.iii.b
		if (!check_pub_key_valid(rom_ext_pub_key)) {
			__REACHABILITY_CHECK

			__CPROVER_assert(!__help_pkey_valid(rom_ext_pub_key),
			"PROPERTY 2: Stop verification if key is invalid");

			continue;
		}

		__REACHABILITY_CHECK

		__CPROVER_assert(__help_pkey_valid(rom_ext_pub_key),
		"PROPERTY 2: Continue verification if key is valid");

		//Step 2.iii.b
		if (!verify_rom_ext_signature(rom_ext_pub_key, current_rom_ext_manifest)) {
			__REACHABILITY_CHECK
			__CPROVER_assert(!__valid_signature[i], 
			"PROPERTY 5: Stop verification if signature is invalid");
			continue;
		}
		__REACHABILITY_CHECK

		__CPROVER_assert(__valid_signature[i],
		"PROPERTY 5: Continue verification if signature is valid");
		__validated_rom_exts[i] = 1; //for CBMC

		//Step 2.iii.d
		PMP_unlock_rom_ext();
				
		__CPROVER_assert(__help_check_pmp_region(i, 0, 1, 0, 1, 1),
		"PROPERTY 10: PMP region 0 should be R, E, and L.");

		//Step 2.iii.e
		if (!final_jump_to_rom_ext(current_rom_ext_manifest)) {
			__REACHABILITY_CHECK

			//Step 2.iv			
			boot_failed_rom_ext_terminated(boot_policy, current_rom_ext_manifest);
			__boot_policy_stop = 1;
			return;
		}
	} // End for

	__REACHABILITY_CHECK

	//Step 2.iv
	boot_failed(boot_policy);
}
