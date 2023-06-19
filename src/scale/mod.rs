//! This module exposes some utilities for working with SCALE bit sequences, namely:
//!
//! - Encoding: see [`encode_using_format`] and [`encode_using_format_to`].
//! - Decoding: see [`decode_using_format_from`].
//! - Talking about obtaining the format of said bit sequences: see the [`mod@format`] module.
//!
//! The [`Decoder`] enum can also return the expected number of bytes to be decoded
//! and the number of bits to be returned without actually decoding them.

mod decode_iter;
mod encode_iter;
use alloc::vec::Vec;
use codec::Error as CodecError;

pub mod format;
// expose the "common" type; rest in `format` module.
pub use format::Format;

/// This is a convenience wrapper around [`encode_using_format_to`].
///
/// # Example
///
/// ```rust
/// use scale_bits::scale::{
///     encode_using_format,
///     format::{ Format, StoreFormat, OrderFormat },
/// };
///
/// let bits = vec![true, true, false, true];
/// let encoded = encode_using_format(
///     bits.into_iter(),
///     Format::new(StoreFormat::U8, OrderFormat::Msb0)
/// );
/// ```
pub fn encode_using_format<I: ExactSizeIterator<Item = bool>>(it: I, format: Format) -> Vec<u8> {
	let mut out = Vec::new();
	encode_using_format_to(it, format, &mut out);
	out
}

/// SCALE encode an iterator of booleans with a known size into a bit sequence using the
/// given format.
///
/// # Example
///
/// ```rust
/// use scale_bits::scale::{
///     encode_using_format_to,
///     format::{ Format, StoreFormat, OrderFormat },
/// };
///
/// let bits = vec![true, true, false, true];
///
/// let mut encoded = Vec::new();
/// encode_using_format_to(
///     bits.into_iter(),
///     Format::new(StoreFormat::U8, OrderFormat::Msb0),
///     &mut encoded
/// );
/// ```
pub fn encode_using_format_to<I: ExactSizeIterator<Item = bool>>(
	it: I,
	format: Format,
	out: &mut Vec<u8>,
) {
	use encode_iter::*;
	use format::{OrderFormat, StoreFormat};
	match (format.store, format.order) {
		(StoreFormat::U8, OrderFormat::Lsb0) => encode_iter_lsb0_u8(it, out),
		(StoreFormat::U8, OrderFormat::Msb0) => encode_iter_msb0_u8(it, out),
		(StoreFormat::U16, OrderFormat::Lsb0) => encode_iter_lsb0_u16(it, out),
		(StoreFormat::U16, OrderFormat::Msb0) => encode_iter_msb0_u16(it, out),
		(StoreFormat::U32, OrderFormat::Lsb0) => encode_iter_lsb0_u32(it, out),
		(StoreFormat::U32, OrderFormat::Msb0) => encode_iter_msb0_u32(it, out),
		(StoreFormat::U64, OrderFormat::Lsb0) => encode_iter_lsb0_u64(it, out),
		(StoreFormat::U64, OrderFormat::Msb0) => encode_iter_msb0_u64(it, out),
	}
}

/// SCALE decode a bit sequence using the given format, handing back an iterator of booleans.
///
/// # Example
///
/// ```rust
/// use scale_bits::scale::{
///     encode_using_format,
///     decode_using_format_from,
///     format::{ Format, StoreFormat, OrderFormat },
/// };
///
/// let bits = vec![true, true, false, true];
///
/// // Encode the bits to have something to decode:
/// let encoded = encode_using_format(
///     bits.iter().copied(),
///     Format::new(StoreFormat::U8, OrderFormat::Msb0)
/// );
///
/// // Decode them again.
/// let decoder = decode_using_format_from(
///     &encoded,
///     Format::new(StoreFormat::U8, OrderFormat::Msb0)
/// ).unwrap();
/// let new_bits: Result<Vec<bool>,_> = decoder.collect();
///
/// assert_eq!(bits, new_bits.unwrap());
/// ```
pub fn decode_using_format_from(
	bytes: &'_ [u8],
	format: Format,
) -> Result<Decoder<'_>, CodecError> {
	use decode_iter::*;
	use format::{OrderFormat, StoreFormat};
	let inner = match (format.store, format.order) {
		(StoreFormat::U8, OrderFormat::Lsb0) => {
			DecodeInner::DecodeLsb0U8(DecodeLsb0U8::new(bytes)?)
		}
		(StoreFormat::U16, OrderFormat::Lsb0) => {
			DecodeInner::DecodeLsb0U16(DecodeLsb0U16::new(bytes)?)
		}
		(StoreFormat::U32, OrderFormat::Lsb0) => {
			DecodeInner::DecodeLsb0U32(DecodeLsb0U32::new(bytes)?)
		}
		(StoreFormat::U64, OrderFormat::Lsb0) => {
			DecodeInner::DecodeLsb0U64(DecodeLsb0U64::new(bytes)?)
		}
		(StoreFormat::U8, OrderFormat::Msb0) => {
			DecodeInner::DecodeMsb0U8(DecodeMsb0U8::new(bytes)?)
		}
		(StoreFormat::U16, OrderFormat::Msb0) => {
			DecodeInner::DecodeMsb0U16(DecodeMsb0U16::new(bytes)?)
		}
		(StoreFormat::U32, OrderFormat::Msb0) => {
			DecodeInner::DecodeMsb0U32(DecodeMsb0U32::new(bytes)?)
		}
		(StoreFormat::U64, OrderFormat::Msb0) => {
			DecodeInner::DecodeMsb0U64(DecodeMsb0U64::new(bytes)?)
		}
	};
	Ok(Decoder { inner })
}

/// This is handed back from [`decode_using_format_from`], and can be used to obtain some information about,
/// or iterate over, the SCALE encoded bit sequence, using the [`Format`] given. Alternately, you can
/// match on it to retrieve a decoder for the specific format, which may be more efficient.
///
/// # Example
///
/// ```rust
/// use scale_bits::scale::{
///     encode_using_format,
///     decode_using_format_from,
///     format::{ Format, StoreFormat, OrderFormat },
/// };
///
/// let bits = vec![true, true, false, true];
///
/// // Encode the bits to have something to decode:
/// let encoded = encode_using_format(
///     bits.iter().copied(),
///     Format::new(StoreFormat::U8, OrderFormat::Msb0)
/// );
///
/// // Obtain a decoder given some SCALE encoded bits in some format.
/// let decoder = decode_using_format_from(
///     &encoded,
///     Format::new(StoreFormat::U8, OrderFormat::Msb0)
/// ).unwrap();
///
/// // We can see how many bits are stored:
/// assert_eq!(decoder.len(), 4);
///
/// // We can see how many bytes are used to store them:
/// assert_eq!(decoder.encoded_size(), encoded.len());
///
/// // Decoder is an iterator, so we can iterate and collect the bits back up:
/// let new_bits: Result<Vec<bool>,_> = decoder.collect();
/// assert_eq!(bits, new_bits.unwrap());
/// ```
#[derive(Clone, Debug)]
pub struct Decoder<'a> {
	inner: DecodeInner<'a>,
}

// [TODO] jsdw: Test performance. Can we scrap the macro stuff to
// generate the various decode_iter types and just have a single type
// to avoid needing to match on an enum arm each time we do something?
// Avoid exposing this so we can do this as a non breaking patch change.
#[derive(Clone, Debug)]
enum DecodeInner<'a> {
	DecodeLsb0U8(decode_iter::DecodeLsb0U8<'a>),
	DecodeLsb0U16(decode_iter::DecodeLsb0U16<'a>),
	DecodeLsb0U32(decode_iter::DecodeLsb0U32<'a>),
	DecodeLsb0U64(decode_iter::DecodeLsb0U64<'a>),
	DecodeMsb0U8(decode_iter::DecodeMsb0U8<'a>),
	DecodeMsb0U16(decode_iter::DecodeMsb0U16<'a>),
	DecodeMsb0U32(decode_iter::DecodeMsb0U32<'a>),
	DecodeMsb0U64(decode_iter::DecodeMsb0U64<'a>),
}

macro_rules! decode_iter_arms {
	($self:ident, $i:ident => $expr:expr) => {{
		let Self { inner } = $self;
		match inner {
			DecodeInner::DecodeLsb0U8($i) => $expr,
			DecodeInner::DecodeLsb0U16($i) => $expr,
			DecodeInner::DecodeLsb0U32($i) => $expr,
			DecodeInner::DecodeLsb0U64($i) => $expr,
			DecodeInner::DecodeMsb0U8($i) => $expr,
			DecodeInner::DecodeMsb0U16($i) => $expr,
			DecodeInner::DecodeMsb0U32($i) => $expr,
			DecodeInner::DecodeMsb0U64($i) => $expr,
		}
	}};
}

impl<'a> Iterator for Decoder<'a> {
	type Item = Result<bool, CodecError>;
	fn next(&mut self) -> Option<Self::Item> {
		decode_iter_arms!(self, i => i.next())
	}
	fn size_hint(&self) -> (usize, Option<usize>) {
		decode_iter_arms!(self, i => i.size_hint())
	}
}
impl<'a> ExactSizeIterator for Decoder<'a> {}

impl<'a> Decoder<'a> {
	/// Return the total number of bytes needed to represent the
	/// SCALE encoded bit sequence we're looking at.
	pub fn encoded_size(&self) -> usize {
		decode_iter_arms!(self, i => i.encoded_size())
	}

	/// Return the remaining bytes.
	pub fn remaining_bytes(&self) -> &[u8] {
		decode_iter_arms!(self, i => i.remaining_bytes())
	}
}

#[cfg(test)]
mod test {
	use super::format::{Format, OrderFormat, StoreFormat};
	use super::*;
	use alloc::vec;
	use bitvec::{
		order::{BitOrder, Lsb0, Msb0},
		store::BitStore,
		vec::BitVec,
	};
	use codec::Encode;

	fn assert_iter_matches_bits<S, O>(bits: BitVec<S, O>, format: Format)
	where
		S: BitStore,
		O: BitOrder,
		BitVec<S, O>: Encode,
	{
		// Encode bitvec:
		let bytes = bits.encode();

		// Turn bitvec to bools:
		let in_bools: Vec<bool> = bits.clone().into_iter().collect();

		// Decode struct:
		let decoder = decode_using_format_from(&bytes, format).unwrap();

		// Does decoder know correct size in bytes?
		assert_eq!(
			decoder.encoded_size(),
			bytes.len(),
			"Wrong size (actual vs expected) for {:?}",
			bits
		);

		// Does decoder return the same bools?
		let out_bools: Result<Vec<bool>, _> = decoder.collect();
		assert_eq!(in_bools, out_bools.expect("can't collect bools"), "Mismatch for {:?}", bits);
	}

	fn assert_iter_bits_all_formats(bits: Vec<u8>) {
		let bits: Vec<bool> = bits
			.into_iter()
			.map(|n| match n {
				0 => false,
				1 => true,
				_ => panic!("only 0 or 1 bits allowed"),
			})
			.collect();

		let b: BitVec<u8, Lsb0> = bits.iter().collect();
		let f = Format::new(StoreFormat::U8, OrderFormat::Lsb0);
		assert_iter_matches_bits(b, f);

		let b: BitVec<u16, Lsb0> = bits.iter().collect();
		let f = Format::new(StoreFormat::U16, OrderFormat::Lsb0);
		assert_iter_matches_bits(b, f);

		let b: BitVec<u32, Lsb0> = bits.iter().collect();
		let f = Format::new(StoreFormat::U32, OrderFormat::Lsb0);
		assert_iter_matches_bits(b, f);

		let b: BitVec<u64, Lsb0> = bits.iter().collect();
		let f = Format::new(StoreFormat::U64, OrderFormat::Lsb0);
		assert_iter_matches_bits(b, f);

		let b: BitVec<u8, Msb0> = bits.iter().collect();
		let f = Format::new(StoreFormat::U8, OrderFormat::Msb0);
		assert_iter_matches_bits(b, f);

		let b: BitVec<u16, Msb0> = bits.iter().collect();
		let f = Format::new(StoreFormat::U16, OrderFormat::Msb0);
		assert_iter_matches_bits(b, f);

		let b: BitVec<u32, Msb0> = bits.iter().collect();
		let f = Format::new(StoreFormat::U32, OrderFormat::Msb0);
		assert_iter_matches_bits(b, f);

		let b: BitVec<u64, Msb0> = bits.iter().collect();
		let f = Format::new(StoreFormat::U64, OrderFormat::Msb0);
		assert_iter_matches_bits(b, f);
	}

	#[test]
	fn test_iter_bits() {
		assert_iter_bits_all_formats(vec![]);
		assert_iter_bits_all_formats(vec![0]);
		assert_iter_bits_all_formats(vec![0, 1]);
		assert_iter_bits_all_formats(vec![0, 0, 0]);
		assert_iter_bits_all_formats(vec![0, 1, 1, 0, 1, 1, 0, 1]);
		assert_iter_bits_all_formats(vec![0, 1, 1, 0, 1, 1, 0, 1, 0]);
		assert_iter_bits_all_formats(vec![0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]);
		assert_iter_bits_all_formats(vec![0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]);
		assert_iter_bits_all_formats(vec![
			0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
			1, 0, 1, 0,
		]);
		assert_iter_bits_all_formats(vec![
			0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
			1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1,
			1, 0, 1, 1, 0, 1,
		]);
		assert_iter_bits_all_formats(vec![
			0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
			1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1,
			1, 0, 1, 1, 0, 1, 0,
		]);
	}
}
