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

// This module contains iterators that take some SCALE encoded bit sequence
// and allow you to iterate over each bit in them as bools.

use codec::{Compact, Decode, Encode, Error as CodecError};

fn bits_in<T>() -> u8 {
	(core::mem::size_of::<T>() * 8) as u8
}

macro_rules! starting_bit {
	(lsb, $ty:ty) => {
		0
	};
	(msb, $ty:ty) => {
		bits_in::<$ty>() - 1
	};
}

macro_rules! next_bit {
	(lsb, $ty:ty, $self:ident) => {
		$self.bit += 1;
		if $self.bit == bits_in::<$ty>() {
			$self.current_byte = None;
			$self.bit = 0;
		}
	};
	(msb, $ty:ty, $self:ident) => {
		if $self.bit == 0 {
			$self.current_byte = None;
			$self.bit = bits_in::<$ty>();
		}
		$self.bit -= 1;
	};
}

macro_rules! decode_iter {
	($order:ident, $name:ident, $ty:ty) => {
		/// An iterator over a SCALE encoded bit sequence.
		#[derive(Clone, Debug)]
		pub struct $name<'a> {
			bytes: &'a [u8],
			current_byte: Option<$ty>,
			bit: u8,
			len: u32,
			remaining_bits: u32,
		}

		impl<'a> $name<'a> {
			/// Create a new iterator over some SCALE encoded bytes.
			pub fn new(bytes: &'a [u8]) -> Result<Self, CodecError> {
				let bytes = &mut &*bytes;

				// Decode length first:
				let len = Compact::<u32>::decode(bytes)?.0;

				Ok(Self {
					bytes,
					current_byte: None,
					bit: starting_bit!($order, $ty),
					len,
					remaining_bits: len,
				})
			}

			/// Return the total number of bytes needed to represent the
			/// SCALE encoded bit sequence we're looking at.
			pub fn encoded_size(&self) -> usize {
				let num_bits = self.len as usize;

				let bytes_per_store = core::mem::size_of::<$ty>();
				let bits_per_store = bytes_per_store * 8;

				// Dividing rounds down, and then multiply by number of bytes.
				let store_bytes_floored = (num_bits / bits_per_store) * bytes_per_store;

				// "undo" the initial rounding down; do we need an extra store unit?
				let store_bits_remainder = num_bits & (bits_per_store - 1);
				// If we rounded down and lost bits, we'll need another store_size el
				// to hold everything. Else we won't.
				let store_bytes = store_bytes_floored
					+ if store_bits_remainder > 0 { bytes_per_store } else { 0 };

				let len_bytes = Compact(self.len).encoded_size();
				len_bytes + store_bytes
			}

			/// Return the remaining bytes.
			pub fn remaining_bytes(&self) -> &[u8] {
				self.bytes
			}
		}

		impl<'a> Iterator for $name<'a> {
			type Item = Result<bool, CodecError>;

			fn next(&mut self) -> Option<Self::Item> {
				// No bits left to decode; we're done.
				if self.remaining_bits == 0 {
					return None;
				}

				// Get the next store entry to pull from:
				let store = match self.current_byte {
					Some(store) => store,
					None => {
						let bytes = &mut &*self.bytes;
						let store = match <$ty>::decode(bytes) {
							Ok(s) => s,
							Err(e) => return Some(Err(e)),
						};

						self.current_byte = Some(store);
						self.bytes = *bytes;
						store
					}
				};

				// Extract a bit:
				let res = match (store >> self.bit) & 1 {
					0 => false,
					1 => true,
					_ => unreachable!("Can only be 0 or 1 owing to &1"),
				};

				// Update records for next bit:
				self.remaining_bits -= 1;
				next_bit!($order, $ty, self);

				Some(Ok(res))
			}

			fn size_hint(&self) -> (usize, Option<usize>) {
				let len = self.remaining_bits as usize;
				(len, Some(len))
			}
		}
		impl<'a> ExactSizeIterator for $name<'a> {}
	};
}

decode_iter!(lsb, DecodeLsb0U8, u8);
decode_iter!(lsb, DecodeLsb0U16, u16);
decode_iter!(lsb, DecodeLsb0U32, u32);
decode_iter!(lsb, DecodeLsb0U64, u64);

decode_iter!(msb, DecodeMsb0U8, u8);
decode_iter!(msb, DecodeMsb0U16, u16);
decode_iter!(msb, DecodeMsb0U32, u32);
decode_iter!(msb, DecodeMsb0U64, u64);

#[cfg(test)]
mod test {
	use super::*;
	use alloc::vec;
	use alloc::vec::Vec;
	use bitvec::{
		order::{Lsb0, Msb0},
		vec::BitVec,
	};
	use codec::Encode;

	macro_rules! assert_iter_matches_bits {
		($bits:expr, $s:ident) => {{
			// Encode bitvec:
			let bytes = $bits.encode();

			// Turn bitvec to bools:
			let in_bools: Vec<bool> = $bits.clone().into_iter().collect();

			// Decode struct:
			let decoder = $s::new(&*bytes).expect("can't parse length");

			// Does decoder know correct size in bytes?
			assert_eq!(
				decoder.encoded_size(),
				bytes.len(),
				"Wrong size (actual vs expected) for {:?}",
				$bits
			);

			// Does decoder return the same bools?
			let out_bools: Result<Vec<bool>, _> = decoder.collect();
			assert_eq!(
				in_bools,
				out_bools.expect("can't collect bools"),
				"Mismatch for {:?}",
				$bits
			);
		}};
	}

	fn assert_iter_bits_all_store_orders(bits: Vec<u8>) {
		let bits: Vec<bool> = bits
			.into_iter()
			.map(|n| match n {
				0 => false,
				1 => true,
				_ => panic!("only 0 or 1 bits allowed"),
			})
			.collect();

		let b: BitVec<u8, Lsb0> = bits.iter().collect();
		assert_iter_matches_bits!(b, DecodeLsb0U8);

		let b: BitVec<u16, Lsb0> = bits.iter().collect();
		assert_iter_matches_bits!(b, DecodeLsb0U16);

		let b: BitVec<u32, Lsb0> = bits.iter().collect();
		assert_iter_matches_bits!(b, DecodeLsb0U32);

		let b: BitVec<u64, Lsb0> = bits.iter().collect();
		assert_iter_matches_bits!(b, DecodeLsb0U64);

		let b: BitVec<u8, Msb0> = bits.iter().collect();
		assert_iter_matches_bits!(b, DecodeMsb0U8);

		let b: BitVec<u16, Msb0> = bits.iter().collect();
		assert_iter_matches_bits!(b, DecodeMsb0U16);

		let b: BitVec<u32, Msb0> = bits.iter().collect();
		assert_iter_matches_bits!(b, DecodeMsb0U32);

		let b: BitVec<u64, Msb0> = bits.iter().collect();
		assert_iter_matches_bits!(b, DecodeMsb0U64);
	}

	#[test]
	fn test_iter_bits() {
		assert_iter_bits_all_store_orders(vec![]);
		assert_iter_bits_all_store_orders(vec![0]);
		assert_iter_bits_all_store_orders(vec![0, 1]);
		assert_iter_bits_all_store_orders(vec![0, 0, 0]);
		assert_iter_bits_all_store_orders(vec![0, 1, 1, 0, 1, 1, 0, 1]);
		assert_iter_bits_all_store_orders(vec![0, 1, 1, 0, 1, 1, 0, 1, 0]);
		assert_iter_bits_all_store_orders(vec![0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]);
		assert_iter_bits_all_store_orders(vec![0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]);
		assert_iter_bits_all_store_orders(vec![
			0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
			1, 0, 1, 0,
		]);
		assert_iter_bits_all_store_orders(vec![
			0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
			1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1,
			1, 0, 1, 1, 0, 1,
		]);
		assert_iter_bits_all_store_orders(vec![
			0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
			1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1,
			1, 0, 1, 1, 0, 1, 0,
		]);
	}
}
