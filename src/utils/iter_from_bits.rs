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

// Iterating over some bools and writing them to bits either lsb or msb.

macro_rules! iter_bits_to_lsb {
	($iter:ident; $ty:ident) => {{
		const SIZE: usize = std::mem::size_of::<$ty>() * 8;
		let mut iter = $iter.into_iter();
		let mut last_byte = 0;
		let mut pos_in_last_byte = 0;

		std::iter::from_fn(move || loop {
			let b = match iter.next() {
				Some(b) => b,
				None => {
					if pos_in_last_byte > 0 {
						pos_in_last_byte = 0;
						return Some(last_byte);
					} else {
						return None;
					}
				}
			};

			let bit = match b {
				true => 1,
				false => 0,
			};
			last_byte |= (bit << pos_in_last_byte);

			if pos_in_last_byte == SIZE as $ty - 1 {
				let next_output = last_byte;
				last_byte = 0;
				pos_in_last_byte = 0;
				return Some(next_output);
			} else {
				pos_in_last_byte += 1;
			}
		})
	}};
}

macro_rules! iter_bits_to_msb {
	($iter:ident; $ty:ident) => {{
		const SIZE: usize = std::mem::size_of::<$ty>() * 8;
		let mut iter = $iter.into_iter();
		let mut last_byte = 0;
		let mut pos_in_last_byte = SIZE as $ty - 1;

		std::iter::from_fn(move || loop {
			let b = match iter.next() {
				Some(b) => b,
				None => {
					if pos_in_last_byte < SIZE as $ty - 1 {
						pos_in_last_byte = SIZE as $ty - 1;
						return Some(last_byte);
					} else {
						return None;
					}
				}
			};

			let bit = match b {
				true => 1,
				false => 0,
			};
			last_byte |= (bit << pos_in_last_byte);

			if pos_in_last_byte == 0 {
				let next_output = last_byte;
				last_byte = 0;
				pos_in_last_byte = SIZE as $ty - 1;
				return Some(next_output);
			} else {
				pos_in_last_byte -= 1;
			}
		})
	}};
}

pub fn iter_bits_to_u8_msb(bits: impl IntoIterator<Item = bool>) -> impl Iterator<Item = u8> {
	iter_bits_to_msb!(bits; u8)
}

pub fn iter_bits_to_u16_lsb(bits: impl IntoIterator<Item = bool>) -> impl Iterator<Item = u16> {
	iter_bits_to_lsb!(bits; u16)
}

pub fn iter_bits_to_u16_msb(bits: impl IntoIterator<Item = bool>) -> impl Iterator<Item = u16> {
	iter_bits_to_msb!(bits; u16)
}

pub fn iter_bits_to_u32_lsb(bits: impl IntoIterator<Item = bool>) -> impl Iterator<Item = u32> {
	iter_bits_to_lsb!(bits; u32)
}

pub fn iter_bits_to_u32_msb(bits: impl IntoIterator<Item = bool>) -> impl Iterator<Item = u32> {
	iter_bits_to_msb!(bits; u32)
}

#[cfg(test)]
mod test {
	use super::*;

	const I: bool = true;
	const O: bool = false;

	#[test]
	fn test_iter_bits() {
		fn v<I: Iterator<Item = T>, T>(i: I) -> Vec<T> {
			i.collect()
		}

		assert_eq!(v(iter_bits_to_u8_msb(vec![])), Vec::<u8>::new());

		assert_eq!(v(iter_bits_to_u8_msb(vec![O, O, I, O, I, I, O, I])), vec![0b00101101]);
		assert_eq!(
			v(iter_bits_to_u8_msb(vec![O, O, I, O, I, I, O, I, I])),
			vec![0b00101101, 0b10000000]
		);

		assert_eq!(
			v(iter_bits_to_u16_msb(vec![O, O, I, O, I, I, O, I, I])),
			vec![0b00101101_10000000]
		);
		assert_eq!(
			v(iter_bits_to_u16_msb(vec![O, O, I, O, I, I, O, I, I, O, I])),
			vec![0b00101101_10100000]
		);
		assert_eq!(
			v(iter_bits_to_u16_msb(vec![O, O, I, O, I, I, O, I, I, O, I, O, O, O, O, O, I])),
			vec![0b00101101_10100000, 0b10000000_00000000]
		);

		assert_eq!(
			v(iter_bits_to_u32_msb(vec![O, O, I, O, I, I, O, I, I, O, I, O, O, O, O, O, I])),
			vec![0b00101101_10100000_10000000_00000000]
		);
		assert_eq!(
			v(iter_bits_to_u32_msb(vec![
				O, O, I, O, I, I, O, I, I, O, I, O, O, O, O, O, I, O, I, O, I, I, O, I, I, O, I, O,
				O, O, O, O, O
			])),
			vec![0b00101101_10100000_10101101_10100000, 0]
		);

		assert_eq!(
			v(iter_bits_to_u16_lsb(vec![O, O, I, O, I, I, O, I, I])),
			vec![0b00000001_10110100]
		);
		assert_eq!(
			v(iter_bits_to_u16_lsb(vec![O, O, I, O, I, I, O, I, I, O, I])),
			vec![0b00000101_10110100]
		);
		assert_eq!(
			v(iter_bits_to_u16_lsb(vec![O, O, I, O, I, I, O, I, I, O, I, O, O, O, O, O, I])),
			vec![0b00000101_10110100, 0b00000000_00000001]
		);

		assert_eq!(
			v(iter_bits_to_u32_lsb(vec![O, O, I, O, I, I, O, I, I, O, I, O, O, O, O, O, I])),
			vec![0b00000000_00000001_00000101_10110100]
		);
		assert_eq!(
			v(iter_bits_to_u32_lsb(vec![
				O, O, I, O, I, I, O, I, I, O, I, O, O, O, O, O, I, O, I, O, I, I, O, I, I, O, I, O,
				O, O, O, O, O
			])),
			vec![0b00000101_10110101_00000101_10110100, 0]
		);
	}
}
