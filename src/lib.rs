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

//! This crate provides the [`Bits`] type; a drop-in, SCALE-compatible replacement for
//! `BitVec<u8, Lsb0>` which can also be encoded-to and decoded-from various store and
//! order types at runtime (`Lsb0` and `Msb0` orderings, and `u8`, `u16` and `u32` store
//! types), allowing for dynamic encoding and decoding based on `scale-info` metadata.

#![deny(missing_docs)]

pub mod bits;
pub mod scale;
