/*
OpenTitan bootcode,
written based on:
sw/device/rom_ext/docs/manifest.md
sw/device/mask_rom/mask_rom.c
sw/device/mask_rom/docs/index.md
doc/security/specs/secure_boot/index.md
*/

#include "hmac.h"
#include "mask_rom.h"

#define PKEY_WHITELIST_SIZE 5

BYTE hmac_key[HMAC_KEY_SIZE];

// Function type used to define function pointer to the entry of the ROM_EXT stage.
typedef void(rom_ext_boot_func)(void); 

// Function type for entry point of boot policy fail function
typedef void(fail_func)(void); 

// Function type for entry point of boot policy fail rom ext terminated function.
typedef void(fail_rom_ext_terminated_func)(rom_ext_manifest_t); 


extern boot_policy_t FLASH_CTRL_read_boot_policy();


extern rom_exts_manifests_t FLASH_CTRL_rom_ext_manifests_to_try(boot_policy_t boot_policy);


extern char* OTBN_RSA_3072_DECRYPT(int32_t* signature, int signature_len, int32_t exponent, int32_t* modulus);


extern pub_key_t* ROM_CTRL_get_whitelist();


extern void PMP_WRITE_REGION(uint8_t reg, uint8_t r, uint8_t w, uint8_t e, uint8_t l);


int verify_rom_ext_signature(pub_key_t rom_ext_pub_key, rom_ext_manifest_t manifest) {

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

	signature_t signature = manifest.signature;

	int result = OTBN_RSASSA_PKCS1_V1_5_VERIFY(rom_ext_pub_key.exponent, rom_ext_pub_key.modulus, message, bytes, signature.value, RSA_SIZE, manifest);

	return result; //0 or 1
}


int OTBN_RSASSA_PKCS1_V1_5_VERIFY(int32_t exponent, int32_t* modulus, char* message, int message_len, int32_t* signature, int signature_len) {
	
	if (signature_len != RSA_SIZE) {
			return 0;
	}

	char* decrypt = OTBN_RSA_3072_DECRYPT(signature, signature_len, exponent, modulus);
	char* hash = HMAC_SHA2_256(hmac_key, message, message_len); //message_len in bytes

	
	if (memcmp(hash, decrypt, 256 / 8) == 0){
		return 1; //verified
	}
	else{
		return 0;
	}
}


pub_key_t read_pub_key(rom_ext_manifest_t current_rom_ext_manifest) {
	return current_rom_ext_manifest.pub_signature_key;
}


int check_pub_key_valid(pub_key_t rom_ext_pub_key){ //assumed behavior behavior of check func
	pub_key_t* pkey_whitelist = ROM_CTRL_get_whitelist();

	for (int i = 0; i < PKEY_WHITELIST_SIZE; i++) {
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


void PMP_unlock_rom_ext() {
	//Read, Execute, Locked the address space of the ROM extension image
	PMP_WRITE_REGION(        0,        1,        0,        1,        1);
	//                  Region      Read     Write	  Execute	  Locked 
}


void PMP_enable_memory_protection() {
	//Apply PMP region 15 to cover entire flash
	PMP_WRITE_REGION(       15,        1,        0,        0,        1);
	//                  Region      Read     Write   Execute    Locked 
}


int final_jump_to_rom_ext(rom_ext_manifest_t current_rom_ext_manifest) { // Returns a boolean value.
	//Execute rom ext code step 2.iii.e
	rom_ext_boot_func* rom_ext_entry = (rom_ext_boot_func*)current_rom_ext_manifest.image_code;

	rom_ext_entry();

	//if rom_ext returns, we should return false 
	//and execute step 2.iv.
	return 0;
}


void boot_failed(boot_policy_t boot_policy) {
	fail_func* fail_func_entry = (fail_func*)boot_policy.fail;
	fail_func_entry();
}


void boot_failed_rom_ext_terminated(boot_policy_t boot_policy, rom_ext_manifest_t current_rom_ext_manifest) {
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


void mask_rom_boot(boot_policy_t boot_policy, rom_exts_manifests_t rom_exts_to_try ){

	boot_policy_t boot_policy = FLASH_CTRL_read_boot_policy();
	rom_exts_manifests_t rom_exts_to_try = FLASH_CTRL_rom_ext_manifests_to_try(boot_policy);

	PMP_enable_memory_protection();

	//Step 2.iii
	for (int i = 0; i < rom_exts_to_try.size; i++) {

		rom_ext_manifest_t current_rom_ext_manifest = rom_exts_to_try.rom_exts_mfs[i];

		signature_t signature = current_rom_ext_manifest.signature;

		if (!check_rom_ext_manifest(current_rom_ext_manifest)) {
			continue;
		}

		//Step 2.iii.b
		pub_key_t rom_ext_pub_key = read_pub_key(current_rom_ext_manifest);	

		//Step 2.iii.b
		if (!check_pub_key_valid(rom_ext_pub_key)) {
			continue;
		}

		//Step 2.iii.b
		if (!verify_rom_ext_signature(rom_ext_pub_key, current_rom_ext_manifest)) {
			continue;
		}
		
		//Step 2.iii.d
		PMP_unlock_rom_ext();

		//Step 2.iii.e
		if (!final_jump_to_rom_ext(current_rom_ext_manifest)) {

			//Step 2.iv			
			boot_failed_rom_ext_terminated(boot_policy, current_rom_ext_manifest);
			return;
		}
	} // End for

	//Step 2.iv
	boot_failed(boot_policy);
}