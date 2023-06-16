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

#![allow(clippy::module_inception)]

use alloc::vec::Vec;
use codec::{Compact, Decode, Encode};

/// This macro makes it trivial to construct [`Bits`] from either 0 and 1 bit
/// literals, or booleans.
///
/// ```rust
/// use scale_bits::bits;
///
/// // Using 1 and 0 literals to represent the bits:
/// let bits = bits![1,1,0,1,0,1];
/// assert_eq!(bits.to_vec(), vec![true, true, false, true, false, true]);
///
/// // Using true and false to represent the bits:
/// let bits = bits![true, true, false, true, false, true];
/// assert_eq!(bits.to_vec(), vec![true, true, false, true, false, true]);
///
/// // These don't have to be literals:
/// let t = true;
/// let f = false;
/// let bits = bits![t,t,f,t,f,t];
/// assert_eq!(bits.to_vec(), vec![true, true, false, true, false, true]);
///
/// # // Empty bits should be fine:
/// # assert_eq!(bits![].to_vec(), Vec::<bool>::new());
/// #
/// # // Trailing ',' should be fine:
/// # assert_eq!(bits![0,].to_vec(), vec![false]);
/// # assert_eq!(bits![1,].to_vec(), vec![true]);
/// # assert_eq!(bits![0,1,].to_vec(), vec![false, true]);
/// # assert_eq!(bits![false,].to_vec(), vec![false]);
/// # assert_eq!(bits![true,].to_vec(), vec![true]);
/// # assert_eq!(bits![false,true,].to_vec(), vec![false, true]);
/// #
/// # // We can mix bools and bits inc expressions
/// # assert_eq!(bits![0,t,1,f].to_vec(), vec![false, true, true, false]);
/// ```
#[macro_export]
macro_rules! bits {
    ($($val:tt),* $(,)*) => {{
        #[allow(unused_mut)]
        let mut bits = $crate::bits::Bits::new();
        $crate::bits!(__internal__ bits: $($val),*);
        bits
    }};
    (__internal__ $bits:ident: 1 $(,$rest:tt)* $(,)?) => {{
        $bits.push(true);
        $crate::bits!(__internal__ $bits: $($rest,)*);
    }};
    (__internal__ $bits:ident: 0 $(,$rest:tt)* $(,)?) => {{
        $bits.push(false);
        $crate::bits!(__internal__ $bits: $($rest,)*);
    }};
    (__internal__ $bits:ident: $bool:expr $(,$rest:tt)* $(,)?) => {{
        $bits.push($bool);
        $crate::bits!(__internal__ $bits: $($rest,)*);
    }};
    (__internal__ $bits:ident: $(,)?) => {{
        // Catch the "empty" case and end.
    }};
}

/// This represents a sequence of boolean values, packed into bits.
///
/// One of the defining features of this type is that it SCALE encodes and decodes into an
/// identical representation to a `BitVec<u8, Lsb0>`, and has matching a [`scale_info::TypeInfo`]
/// implementation to align with this. This allows it to be used in place of `BitVec<u8, Lsb0>`
/// when you need something with an identical SCALE representation and a simple API and don't wish
/// to pull in the `bitvec` crate.
///
/// In addition to this, we can use the [`crate::scale::Format`] type to encode and decode [`Bits`]
/// in the same way as `BitVec`'s do with order types of `Lsb0` and `Msb0`, and store types of
/// `u8`, `u16`, and `u32`.
///
/// With the `serde` feature enabled we can also serialize and seserialize [`Bits`] from sequences
/// of booleans.
///
/// # Example
///
/// ```rust
/// use scale_bits::bits::Bits;
///
/// let mut bits = Bits::new();
/// bits.push(true);
/// bits.push(false);
/// bits.push(false);
///
/// assert_eq!(bits.len(), 3);
/// ```
///
/// Converting to and from `Vec<bool>`:
///
/// ```rust
/// use scale_bits::bits::Bits;
///
/// let bools = vec![true, false, true, false, true];
/// let bits: Bits = bools.into_iter().collect();
///
/// let new_bools: Vec<bool> = bits.into_iter().collect();
/// assert_eq!(new_bools, vec![true, false, true, false, true]);
/// ```
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Bits {
	pub(crate) storage: Vec<u8>,
	// Number of bits stored in the last byte.
	pub(crate) bits_in_last_byte: usize,
}

impl Bits {
	/// Create a new empty list of bits. This does not allocate.
	pub fn new() -> Self {
		Self::default()
	}

	/// Create a new empty list of bits. Pre-allocates enough space for
	/// the number of bits provided here.
	pub fn with_capacity(num_bits: usize) -> Self {
		let mut num_bytes = num_bits / 8;

		// the above division rounds down, so add another byte
		// if we don't have an exact multiple of 8 num_bits.
		let is_exact_multiple_of_8 = num_bits & 0b111 == 0;
		if !is_exact_multiple_of_8 {
			num_bytes += 1;
		}

		Bits { storage: Vec::with_capacity(num_bytes), bits_in_last_byte: 0 }
	}

	/// Returns true if no bits are stored.
	///
	/// # Example
	///
	/// ```rust
	/// use scale_bits::bits::Bits;
	///
	/// let mut bits = Bits::new();
	/// assert!(bits.is_empty());
	///
	/// bits.push(true);
	/// assert!(!bits.is_empty());
	///
	/// bits.pop();
	/// assert!(bits.is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.storage.is_empty()
	}

	/// Return the number of bits stored.
	///
	/// # Example
	///
	/// ```rust
	/// use scale_bits::bits::Bits;
	///
	/// let mut bits = Bits::new();
	/// assert_eq!(bits.len(), 0);
	///
	/// bits.push(true);
	/// bits.push(false);
	/// bits.push(true);
	/// assert_eq!(bits.len(), 3);
	///
	/// bits.pop();
	/// bits.pop();
	/// assert_eq!(bits.len(), 1);
	pub fn len(&self) -> usize {
		let len = self.storage.len();

		// -1 below so explicit return is zero.
		if len == 0 {
			return 0;
		}

		// minus the last byte worth and then add on only the bits we've
		// stored so far in it.
		(len - 1) * 8 + self.bits_in_last_byte
	}

	/// Push new bits to the end of the list.
	///
	/// # Example
	///
	/// ```rust
	/// use scale_bits::{ bits::Bits, bits };
	///
	/// let mut bs = Bits::new();
	/// bs.push(true);
	/// bs.push(false);
	/// bs.push(true);
	///
	/// assert_eq!(bs, bits![1,0,1]);
	/// ```
	pub fn push(&mut self, b: bool) {
		let bit_val: u8 = match b {
			true => 1,
			false => 0,
		};

		match self.bits_in_last_byte {
			// empty storage is the only time we see 0
			// and a full last byte is when we see 8. In
			// both cases we start a new byte with our 1
			// value.
			0 | 8 => {
				self.storage.push(bit_val);
				self.bits_in_last_byte = 1;
			}
			// Otherwise, get the last byte and add our
			// bit in at the right offset.
			n => {
				let byte = self.storage.last_mut().expect("should be a byte");
				*byte |= bit_val << n;
				self.bits_in_last_byte += 1;
			}
		}
	}

	/// Remove bits from the end of the list, returning them
	/// if they are present.
	///
	/// # Example
	///
	/// ```rust
	/// use scale_bits::{ bits::Bits, bits };
	///
	/// let mut bs = bits![true, false, true, true];
	/// assert_eq!(bs.pop(), Some(true));
	/// assert_eq!(bs.pop(), Some(true));
	/// assert_eq!(bs.pop(), Some(false));
	/// assert_eq!(bs.pop(), Some(true));
	/// assert_eq!(bs.pop(), None);
	/// assert_eq!(bs.pop(), None);
	/// ```
	pub fn pop(&mut self) -> Option<bool> {
		let last_byte = self.storage.last_mut()?;

		// 0 bits in last byte should never happen. minus one so:
		// - bits == 1? don't right shift
		// - bits == 2? shift the one bit before it off
		// - .. and so on.
		let right_shift_amount = self.bits_in_last_byte - 1;

		let res = match (*last_byte >> right_shift_amount) & 1 {
			1 => true,
			0 => false,
			_ => unreachable!("Can only be 0 or 1 owing to &1"),
		};

		// zero out the entry we're returning.
		*last_byte ^= 1 << right_shift_amount;

		// decrement our count of bits in the last byte:
		self.bits_in_last_byte -= 1;
		// if 0, remove the byte from the vec entirely:
		if self.bits_in_last_byte == 0 {
			self.storage.pop();
			if self.storage.is_empty() {
				self.bits_in_last_byte = 0;
			} else {
				self.bits_in_last_byte = 8;
			}
		}

		Some(res)
	}

	/// Retrieve a bit at a given index, returning `None` if no bit exists
	/// at that index.
	///
	/// # Example
	///
	/// ```rust
	/// use scale_bits::bits;
	///
	/// let bs = bits![true, false, true, true];
	/// assert_eq!(bs.get(0), Some(true));
	/// assert_eq!(bs.get(1), Some(false));
	/// assert_eq!(bs.get(2), Some(true));
	/// assert_eq!(bs.get(3), Some(true));
	/// assert_eq!(bs.get(4), None);
	/// ```
	pub fn get(&self, idx: usize) -> Option<bool> {
		// Bail early if empty storage since we'll expect
		// at least one item to be stored below.
		if self.storage.is_empty() {
			return None;
		}

		let byte_idx = idx / 8;
		// Dividing rounds down; taking last 3 bits gives us that precision back.
		let bit_in_byte = idx & 0b111;

		// Expect at least 1 item to be stored. If we're accessing
		// the last byte, check we have stored enough bits in it.
		if byte_idx == self.storage.len() - 1 && bit_in_byte >= self.bits_in_last_byte {
			return None;
		}

		let byte = *self.storage.get(byte_idx)?;
		match (byte >> bit_in_byte) & 1 {
			0 => Some(false),
			1 => Some(true),
			_ => unreachable!("Can only be 0 or 1 owing to &1"),
		}
	}

	/// Iterate over each bit in order, returning `true` or `false` for each.
	///
	/// # Example
	///
	/// ```rust
	/// use scale_bits::bits;
	///
	/// let bs = bits![true, false, true, true];
	///
	/// let v: Vec<bool> = bs.iter().collect();
	/// assert_eq!(v, vec![true, false, true, true]);
	/// ```
	pub fn iter(&'_ self) -> BitsIter<'_> {
		BitsIter { pos: 0, bits: self }
	}

	/// Convert our bits into a `Vec<bool>`.
	///
	/// # Example
	///
	/// ```rust
	/// use scale_bits::bits;
	///
	/// let bs = bits![true, false, true, true].to_vec();
	/// assert_eq!(bs, vec![true, false, true, true]);
	/// ```
	pub fn to_vec(self) -> Vec<bool> {
		self.into_iter().collect()
	}
}

impl core::iter::IntoIterator for Bits {
	type Item = bool;
	type IntoIter = BitsIntoIter;

	fn into_iter(self) -> Self::IntoIter {
		BitsIntoIter { pos: 0, bits: self }
	}
}

/// Returned from calling `into_iter` on [`Bits`] via the
/// [`std::iter::IntoIterator`] trait. Allows iteration over
/// each stored bit.
#[derive(Clone, Debug)]
pub struct BitsIntoIter {
	pos: usize,
	bits: Bits,
}

impl Iterator for BitsIntoIter {
	type Item = bool;
	fn next(&mut self) -> Option<Self::Item> {
		let next = self.bits.get(self.pos)?;
		self.pos += 1;
		Some(next)
	}
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.bits.len() - self.pos;
		(len, Some(len))
	}
}
impl ExactSizeIterator for BitsIntoIter {}

/// Returned from calling [`Bits::iter()`]. Allows iteration
/// over each stored bit.
#[derive(Copy, Clone, Debug)]
pub struct BitsIter<'a> {
	pos: usize,
	bits: &'a Bits,
}

impl<'a> Iterator for BitsIter<'a> {
	type Item = bool;
	fn next(&mut self) -> Option<Self::Item> {
		let next = self.bits.get(self.pos)?;
		self.pos += 1;
		Some(next)
	}
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.bits.len() - self.pos;
		(len, Some(len))
	}
}
impl<'a> ExactSizeIterator for BitsIter<'a> {}

impl core::iter::FromIterator<bool> for Bits {
	fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
		let iter = iter.into_iter();

		// if we know the max size, make that space available.
		// otherwise make at least the min size available.
		let num_bits_to_alloc_for = match iter.size_hint() {
			(_, Some(max)) => max,
			(min, None) => min,
		};

		let mut bits = Bits::with_capacity(num_bits_to_alloc_for);
		for b in iter {
			bits.push(b);
		}
		bits
	}
}

impl Decode for Bits {
	fn decode<I: codec::Input>(input: &mut I) -> Result<Self, codec::Error> {
		let len_bits = Compact::<u32>::decode(input)?.0 as usize;
		let remainder = len_bits & 0b111;
		let len = len_bits / 8 + if remainder > 0 { 1 } else { 0 };

		// Just a little safety in case the encoding is naff/malicious; don't
		// pre-allocate more than 1kb to store the bits into.
		const MAX_PRE_ALLOC_BYTES: usize = 1024;
		let prealloc_len = len.min(MAX_PRE_ALLOC_BYTES);
		let mut storage = Vec::with_capacity(prealloc_len);

		for _ in 0..len {
			// THe "native" decoding/encoding of bits is equal to a BitVec<u8, Lsb0>.
			// We just push/read the stored bytes to encode/decode to this format.
			let byte = input.read_byte()?;
			storage.push(byte);
		}

		// if length was greater than 0 and remainder == 0, bits_in_last_byte must be
		// 8 (ie the last byte is full and no remainder). Else, bits_in_last_byte is
		// equal to the remainder.
		let bits_in_last_byte = if !storage.is_empty() && remainder == 0 { 8 } else { remainder };

		Ok(Bits { storage, bits_in_last_byte })
	}
}

impl Encode for Bits {
	fn size_hint(&self) -> usize {
		self.encoded_size()
	}

	fn encode(&self) -> Vec<u8> {
		let mut r = Vec::with_capacity(self.size_hint());

		Compact(self.len() as u32).encode_to(&mut r);
		for byte in &self.storage {
			r.push(*byte);
		}

		r
	}

	fn encoded_size(&self) -> usize {
		// encoding is just compact encoded number of bits and then the bytes to store them all,
		// rounded to u8 because we mirror the encoding for a BitVec<u8, Lsb0>.
		let compact_byte_len = Compact(self.len() as u32).encoded_size();
		compact_byte_len + self.storage.len()
	}
}

#[cfg(feature = "scale-info")]
mod type_info {
	use scale_info::{build::Fields, Path, Type, TypeDefBitSequence, TypeInfo};

	impl TypeInfo for super::Bits {
		type Identity = Self;

		fn type_info() -> Type {
			// Copied from `scale-info`'s bitvec impls; this avoids us needing
			// to import bitvec but ensures we're compatible in terms of the type def.
			enum Lsb0 {}
			impl TypeInfo for Lsb0 {
				type Identity = Self;
				fn type_info() -> Type {
					Type::builder()
						.path(Path::new("Lsb0", "bitvec::order"))
						.composite(Fields::unit())
				}
			}

			TypeDefBitSequence::new::<u8, Lsb0>().into()
		}
	}
}
