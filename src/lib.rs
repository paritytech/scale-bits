// Copyright (C) 2022 Parity Technologies (UK) Ltd. (admin@parity.io)
// This file is a part of the scale-value crate.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//         http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! This small utility crate provides two separate things:
//!
//! 1. A [`Bits`] type that can be SCALE encoded and decoded, and is fully
//!    SCALE compatible with a `BitVec<u8, Lsb0>`. It's a deliberately simple
//!    type that is conceptually just a sequence of bools, and can be used as
//!    a replacement for `BitVec` when you don't need the additional complexity
//!    and functionality that it comes with. See the [`mod@bits`] module for more.
//! 2. Utility methods to help encode and decode arbitrary bit sequences from their
//!    SCALE representation, or skip over the corresponding bytes entirely, with zero
//!    allocations. These bypass the need to first go via some `BitVec` with the
//!    right store/order type, and are WASM compatible (unlike `BitVec`'s `u64` store
//!    type). See the [`scale`] module for more.
//!
//! These things play nicely together (ie you can encode and decode arbitrary bit
//! sequences directly into the [`Bits`] type), but don't need to be used together.

#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub mod bits;
pub mod scale;

// Export the common things at root:

pub use bits::Bits;
pub use scale::{
	decode_using_format_from, encode_using_format, encode_using_format_to, format::Format,
};
