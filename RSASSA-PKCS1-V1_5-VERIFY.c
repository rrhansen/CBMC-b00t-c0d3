#include "sha2-256.h"
#include "RSASSA-PKCS1-V1_5-VERIFY.h"
#include "memory.h"


int __check_params(int32_t exponent, int32_t* modulus, char* message, int message_len, int32_t* signature, int signature_len, rom_ext_manifest_t __current_rom_ext_mf) {

	//Check that public key matches key in manifest
	int __correct_exponent = exponent == __current_rom_ext_mf.pub_signature_key.exponent;

	int __correct_modulus = memcmp(
								modulus,
								__current_rom_ext_mf.pub_signature_key.modulus,
								RSA_SIZE) == 0;

	//Check that signature matches matches signature in manifest 
	int __correct_signature = memcmp(
								signature,
								__current_rom_ext_mf.signature.value,
								RSA_SIZE) == 0;


	//Check that message is correct
	int __correct_msg1 = memcmp(
		message,
		&__current_rom_ext_mf.pub_signature_key,
		sizeof(__current_rom_ext_mf.pub_signature_key)
	) == 0;

	int __correct_msg2 = memcmp(
		message + sizeof(__current_rom_ext_mf.pub_signature_key),
		&__current_rom_ext_mf.image_length,
		sizeof(__current_rom_ext_mf.image_length)
	) == 0;

	int __correct_msg3 = memcmp(
		message + sizeof(__current_rom_ext_mf.pub_signature_key) + sizeof(__current_rom_ext_mf.image_length),
		__current_rom_ext_mf.image_code,
		__current_rom_ext_mf.image_length
	) == 0;

	return __correct_exponent && __correct_modulus && __correct_signature &&
		__correct_msg1 && __correct_msg2 && __correct_msg3;

}


char* RSA_3072_DECRYPT(int32_t* signature, int signature_len, int32_t exponent, int32_t* modulus){
	char* decrypt = malloc(256/8); //model it to be ok for PROPERTY 5
	return decrypt;
}

int RSASSA_PKCS1_V1_5_VERIFY(int32_t exponent, int32_t* modulus, char* message, int message_len, int32_t* signature, int signature_len, rom_ext_manifest_t __current_rom_ext_mf){
	__CPROVER_assert(__CPROVER_OBJECT_SIZE(message) == message_len,
	"PROPERTY 5: Formal parameter message_len lenght matches actual message length.");

	__CPROVER_assert(__CPROVER_OBJECT_SIZE(signature) * 8 == RSA_SIZE*32,
	"PROPERTY 5: Signature to be verified is 3072-bits.");

	__CPROVER_assert(__CPROVER_OBJECT_SIZE(signature) == signature_len * sizeof(int32_t),
	"PROPERTY 5: Formal parameter signature lenght matches actual signature length.");

	__CPROVER_assert(sizeof(exponent) * 8 == 32,
	"PROPERTY 5: Public key exponent is 32 bits.");

	__CPROVER_assert((sizeof(pub_key_t) - sizeof(exponent)) * 8 == RSA_SIZE*32,
	"PROPERTY 5: Public key modulus is 3072-bits."); 

	__CPROVER_assert(__check_params(exponent, modulus, message, message_len, signature, signature_len, __current_rom_ext_mf),
	"PROPERTY 5: Check that key, signature, and message is correct.");

	__REACHABILITY_CHECK

	if(signature_len != RSA_SIZE){
		__CPROVER_assert(signature_len * 32 != RSA_SIZE*32,
		"PROPERTY 5: Length checking: If the length of the signature is not 3072 bytes, stop."); 
		__REACHABILITY_CHECK // Not reachable atm

		return 0;
	}
	__REACHABILITY_CHECK

	int32_t* decrypt = RSA_3072_DECRYPT(signature, signature_len, exponent, modulus);
	char* hash = SHA2_256(message, message_len, __current_rom_ext_mf); //message_len in bytes

	__CPROVER_assert(__CPROVER_OBJECT_SIZE(decrypt)==256/8, 
	"PROPERTY 5: Decrypted message is 256 bits"); 

	__CPROVER_assert(__CPROVER_r_ok(decrypt, 256/8),
	"PROPERTY 5: Decrypted message is in readable address"); 

	__CPROVER_assert(__CPROVER_OBJECT_SIZE(hash)==256/8, 
	"PROPERTY 3: Hash is 256 bits"); 

	__CPROVER_assert(__CPROVER_r_ok(hash, 256/8),
	"PROPERTY 3: hash is in readable address"); 

	if(memcmp(hash, decrypt, RSA_SIZE*sizeof(int32_t))==0)
		return 1; //verified
	else
		return 0;
}