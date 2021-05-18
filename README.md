# b00t-c0d3
The goal is to verify the security of the boot code using CBMC

mask_rom_boot_code.c contains the unaltered boot code without annotations. The boot code is simplified and inspired by OpenTitan's secure boot.


### Verified
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
- [x] Attack Fail Function (vulnerability found)
- [x] Attack Image Length (vulnerability found)
- [x] Attack PMP (vulnerability found)
- [x] Attack OTBN (no vulnerability detectable)
- [x] Attack Hash/HMAC (vulnerability found)
- [x] Attack Whitelist Tamper (vulnerability found)
- [x] Attack Whitelist Fail Functions  (vulnerability found)
