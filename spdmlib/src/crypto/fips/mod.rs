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

mod cavs_vectors;

use crate::error::SpdmResult;

#[test]
pub fn run_self_tests() -> SpdmResult {
    // aead
    match aead_st::run_self_tests() {
        Ok(v) => v,
        Err(e) => return Err(e),
    };

    // asym_verify
    match asym_verify_st::run_self_tests() {
        Ok(v) => v,
        Err(e) => return Err(e),
    };

    // dhe
    match dhe_st::run_self_tests() {
        Ok(v) => v,
        Err(e) => return Err(e),
    };

    // hash
    match hash_st::run_self_tests() {
        Ok(v) => v,
        Err(e) => return Err(e),
    };

    Ok(())
}