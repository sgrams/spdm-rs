// Copyright (c) 2024 Intel Corporation
//
// SPDX-License-Identifier: Apache-2.0 or MIT
//
//

use super::*;

mod aead_st;
mod asym_verify_st;
mod dhe_st;
mod hash_st;
mod hkdf_st;
mod hmac_st;
mod cavs_vectors;

#[derive(Debug)]
pub enum SelfTestError {
    SelfTestFailed,
    Unsupported
}

#[test]
pub fn run_self_tests() -> Result<(), SelfTestError> {
    // aead
    match aead_st::run_self_test() {
        Ok(v) => v,
        Err(e) => return Err(e),
    };

    // asym_verify
    // TBD

    // dhe
    // TBD

    // hash
    match hash_st::run_self_test() {
        Ok(v) => v,
        Err(e) => return Err(e),
    };

    // hkdf
    // TBD

    // hmac
    match hmac_st::run_self_test() {
        Ok(v) => v,
        Err(e) => return Err(e),
    };

    Ok(())
}
