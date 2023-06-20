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

// This module contains functions which take an iterator of bools with known
// sizes and encodes them to bitvecs of different shapes.

use alloc::vec::Vec;
use codec::{Compact, Encode};

fn bits_in<T>() -> usize {
	core::mem::size_of::<T>() * 8
}

macro_rules! encode_iter_lsb {
	($name:ident, $ty:ty) => {
		pub fn $name<I: ExactSizeIterator<Item = bool>>(mut iter: I, out: &mut Vec<u8>) {
			let len = iter.len();
			Compact(len as u32).encode_to(out);

			let mut next_store: $ty = 0;
			let mut pos_in_next_store: $ty = 0;
			while let Some(b) = iter.next() {
				let bit = match b {
					true => 1,
					false => 0,
				};
				next_store |= bit << pos_in_next_store;

				pos_in_next_store += 1;
				if pos_in_next_store == bits_in::<$ty>() as $ty {
					pos_in_next_store = 0;
					next_store.encode_to(out);
					next_store = 0;
				}
			}

			if pos_in_next_store > 0 {
				next_store.encode_to(out);
			}
		}
	};
}

macro_rules! encode_iter_msb {
	($name:ident, $ty:ty) => {
		pub fn $name<I: ExactSizeIterator<Item = bool>>(mut iter: I, out: &mut Vec<u8>) {
			let len = iter.len();
			Compact(len as u32).encode_to(out);

			let mut next_store: $ty = 0;
			let mut pos_in_next_store: $ty = bits_in::<$ty>() as $ty - 1;
			while let Some(b) = iter.next() {
				let bit = match b {
					true => 1,
					false => 0,
				};
				next_store |= bit << pos_in_next_store;

				if pos_in_next_store == 0 {
					pos_in_next_store = bits_in::<$ty>() as $ty;
					next_store.encode_to(out);
					next_store = 0;
				}
				pos_in_next_store -= 1;
			}

			if pos_in_next_store < bits_in::<$ty>() as $ty - 1 {
				next_store.encode_to(out);
			}
		}
	};
}

encode_iter_lsb!(encode_iter_lsb0_u8, u8);
encode_iter_lsb!(encode_iter_lsb0_u16, u16);
encode_iter_lsb!(encode_iter_lsb0_u32, u32);
encode_iter_lsb!(encode_iter_lsb0_u64, u64);

encode_iter_msb!(encode_iter_msb0_u8, u8);
encode_iter_msb!(encode_iter_msb0_u16, u16);
encode_iter_msb!(encode_iter_msb0_u32, u32);
encode_iter_msb!(encode_iter_msb0_u64, u64);

#[cfg(test)]
mod test {
	use super::*;
	use alloc::vec;
	use bitvec::{
		order::{Lsb0, Msb0},
		vec::BitVec,
	};
	use codec::Encode;

	macro_rules! assert_encode_matches_bitvec {
		($bits:expr, $fn:ident) => {{
			let bitvec_bytes = $bits.encode();
			let mut out = Vec::new();
			$fn($bits.clone().into_iter(), &mut out);
			assert_eq!(bitvec_bytes, out, "failed to encode {:?}", $bits);
		}};
	}

	fn assert_encode_all_store_orders(bits: Vec<u8>) {
		let bits: Vec<bool> = bits
			.into_iter()
			.map(|n| match n {
				0 => false,
				1 => true,
				_ => panic!("only 0 or 1 bits allowed"),
			})
			.collect();

		let b: BitVec<u8, Lsb0> = bits.iter().collect();
		assert_encode_matches_bitvec!(b, encode_iter_lsb0_u8);

		let b: BitVec<u16, Lsb0> = bits.iter().collect();
		assert_encode_matches_bitvec!(b, encode_iter_lsb0_u16);

		let b: BitVec<u32, Lsb0> = bits.iter().collect();
		assert_encode_matches_bitvec!(b, encode_iter_lsb0_u32);

		let b: BitVec<u64, Lsb0> = bits.iter().collect();
		assert_encode_matches_bitvec!(b, encode_iter_lsb0_u64);

		let b: BitVec<u8, Msb0> = bits.iter().collect();
		assert_encode_matches_bitvec!(b, encode_iter_msb0_u8);

		let b: BitVec<u16, Msb0> = bits.iter().collect();
		assert_encode_matches_bitvec!(b, encode_iter_msb0_u16);

		let b: BitVec<u32, Msb0> = bits.iter().collect();
		assert_encode_matches_bitvec!(b, encode_iter_msb0_u32);

		let b: BitVec<u64, Msb0> = bits.iter().collect();
		assert_encode_matches_bitvec!(b, encode_iter_msb0_u64);
	}

	#[test]
	fn test_encode_bits() {
		assert_encode_all_store_orders(vec![]);
		assert_encode_all_store_orders(vec![0]);
		assert_encode_all_store_orders(vec![0, 1, 1, 0, 1, 1, 0, 1, 0]);
		assert_encode_all_store_orders(vec![0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]);
		assert_encode_all_store_orders(vec![0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]);
		assert_encode_all_store_orders(vec![
			0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
			1, 0, 1, 0,
		]);
		assert_encode_all_store_orders(vec![
			0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
			1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1,
			1, 0, 1, 1, 0, 1,
		]);
		assert_encode_all_store_orders(vec![
			0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
			1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1,
			1, 0, 1, 1, 0, 1, 0,
		]);
	}
}
