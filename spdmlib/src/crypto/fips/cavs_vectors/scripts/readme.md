# Description
Script [`cavs_to_rust.py`](cavs_to_rust.py) can be used to generate Rust structures with CAVS
data input vectors based on data provided by NIST (https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program)

# Usage
Script provides the following options:

* "-i", "--input": Mandatory. Allows user to provide CAVS input data vectors file (*.rsp) taken from NIST. Examples: [SHA256](cavs_vectors_sha256.rsp), [AEAD GCM256 encrypt](cavs_vectors_gcm256_encrypt.rsp), [AEAD GCM256 decrypt](cavs_vectors_gcm256_decrypt.rsp).
* "-m", "--mapping": Mandatory. Allows user to provide json file with mapping between CAVS vectors file attributes ('Msg', 'MD', 'Key', 'IV', 'PT', 'AAD', 'CT', 'Tag') and Rust structure field names ('msg', 'md', 'key', 'iv', 'pt', 'aad', 'ct', 'tag') as well as types ('u32', 'Vec<u8>'). Examples: [SHA256](mapping_sha.json), [AEAD GCM256](mapping_gcm.json).
* "-f", "--filter": Optional. Allows user to provide json file with filter for CAVS vectors paramters ('Keylen', 'IVlen', 'PTlen', 'AADlen', 'Taglen'). CAVS vectors files from NIST contains multiple test cases with different configuration. Some of them may not apply for specific user's test case so this option allows to filter out all the irrelevant test cases from CAVS vectors from NIST. Example: [AEAD GCM256](filter_gcm256.json).
* "-o", "--output": Mandatory. Allows user to provide *.ru file which will be filled with Rust structures keeping CAVS vectors. Examples: [SHA256](../sha256.rs), [AEAD GCM256 encrypt](../gcm256_encrypt.rs), [AEAD GCM256 decrypt](../gcm256_decrypt.rs).

# Examples

SHA-256
```
python3 cavs_to_rust.py -i cavs_vectors_sha256.rsp -m mapping_sha.json -o ../sha256.rs
```

AEAD (AES-256-GCM) encryption
```
python3 cavs_to_rust.py -i cavs_vectors_gcm256_encrypt.rsp -m mapping_gcm.json -f filter_gcm256.json -o ../gcm256_encrypt.rs
```

AEAD (AES-256-GCM) decryption
```
python3 cavs_to_rust.py -i cavs_vectors_gcm256_decrypt.rsp -m mapping_gcm.json -f filter_gcm256.json -o ../gcm256_decrypt.rs
```
