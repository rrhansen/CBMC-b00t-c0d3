# b00t-c0d3
The goal is to verify the security of the boot code using CBMC

mask_rom_boot_code.c contains the unaltered boot code without annotations. The boot code is inspired by the OpenTitan's secure boot pseudocode and specification. The unaltered boot code can be found at https://github.com/KVISDAOWNER/b00t-c0d3.


### Verified
A description of the properties can be found in properties.pdf.
- [x] Property 1
- [x] Property 2
- [x] Property 3
- [x] Property 4
- [x] Property 5
- [x] Property 6
- [x] Property 7
- [x] Property 8
- [x] Property 9
- [x] Property 10

## Attacks (each has their own branch)
- [x] Attack Fail Function 
- [x] Attack Image Length 
- [x] Attack PMP
- [x] Attack OTBN (no vulnerability detectable)
- [x] Attack Hash/HMAC 
- [x] Attack Whitelist Tamper 
- [x] Attack Whitelist Fail Functions 
