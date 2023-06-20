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

//! Ths module defines a [`Format`], which is basically a [`StoreFormat`] and an
//! [`OrderFormat`] and describes the different possible wire formats of a bit sequence.

use alloc::string::String;
#[cfg(feature = "scale-info")]
use alloc::string::ToString;

/// A description of the format used to SCALE encode some bits.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Format {
	/// The [`StoreFormat`] defines the size of each chunk that's written (eg u8, u16 etc).
	pub store: StoreFormat,
	/// The [`OrderFormat`] determines the order in which we write bits to the store type;
	/// do we write to the least significant bit first and work up, or write to the most
	/// significant byte first and work down.
	pub order: OrderFormat,
}

impl Format {
	/// Define a new format by providing a store and order.
	///
	/// # Example
	///
	/// ```rust
	/// use scale_bits::scale::format::{ Format, StoreFormat, OrderFormat };
	///
	/// let format = Format::new(StoreFormat::U8, OrderFormat::Lsb0);
	/// ```
	pub fn new(store: StoreFormat, order: OrderFormat) -> Self {
		Format { store, order }
	}
	/// Use metadata to obtain details about the format.
	#[cfg(feature = "scale-info")]
	pub fn from_metadata(
		ty: &scale_info::TypeDefBitSequence<scale_info::form::PortableForm>,
		types: &scale_info::PortableRegistry,
	) -> Result<Format, FromMetadataError> {
		let bit_store_ty = ty.bit_store_type.id;
		let bit_order_ty = ty.bit_order_type.id;

		// What is the backing store type expected?
		let bit_store_def = &types
			.resolve(bit_store_ty)
			.ok_or(FromMetadataError::StoreFormatNotFound(bit_store_ty))?
			.type_def;

		// What is the bit order type expected?
		let bit_order_def = types
			.resolve(bit_order_ty)
			.ok_or(FromMetadataError::OrderFormatNotFound(bit_order_ty))?
			.path
			.ident()
			.ok_or(FromMetadataError::NoBitOrderIdent)?;

		use scale_info::{TypeDef, TypeDefPrimitive};
		let bit_store_out = match bit_store_def {
			TypeDef::Primitive(TypeDefPrimitive::U8) => Some(StoreFormat::U8),
			TypeDef::Primitive(TypeDefPrimitive::U16) => Some(StoreFormat::U16),
			TypeDef::Primitive(TypeDefPrimitive::U32) => Some(StoreFormat::U32),
			TypeDef::Primitive(TypeDefPrimitive::U64) => Some(StoreFormat::U64),
			_ => None,
		}
		.ok_or_else(|| {
			FromMetadataError::StoreFormatNotSupported(alloc::format!("{bit_store_def:?}"))
		})?;

		let bit_order_out = match &*bit_order_def {
			"Lsb0" => Some(OrderFormat::Lsb0),
			"Msb0" => Some(OrderFormat::Msb0),
			_ => None,
		}
		.ok_or(FromMetadataError::OrderFormatNotSupported(bit_order_def.to_string()))?;

		Ok(Format { store: bit_store_out, order: bit_order_out })
	}
}

/// This is a runtime representation of the order that bits will be written
/// to the specified [`StoreFormat`].
///
/// - [`OrderFormat::Lsb0`] means that we write to the least significant bit first
///   and then work our way up to the most significant bit as we push new bits.
/// - [`OrderFormat::Msb0`] means that we write to the most significant bit first
///   and then work our way down to the least significant bit as we push new bits.
///
/// These are equivalent to `bitvec`'s `order::Lsb0` and `order::Msb0`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum OrderFormat {
	/// Least significant bit first.
	Lsb0,
	/// Most significant bit first.
	Msb0,
}

/// This is a runtime representation of the store type that we're targeting. These
/// are equivalent to the `bitvec` store types `u8`, `u16` and so on.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum StoreFormat {
	/// Equivalent to [`u8`].
	U8,
	/// Equivalent to [`u16`].
	U16,
	/// Equivalent to [`u32`].
	U32,
	/// Equivalent to [`u64`].
	U64,
}

/// An error that can occur when we try to encode or decode to a SCALE bit sequence type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FromMetadataError {
	/// The registry did not contain the bit order type listed.
	OrderFormatNotFound(u32),
	/// The registry did not contain the bit store type listed.
	StoreFormatNotFound(u32),
	/// The bit order type did not have a valid identifier/name.
	NoBitOrderIdent,
	/// The bit store type that we found was not what we expected (a primitive u8/u16/u32/u64).
	StoreFormatNotSupported(String),
	/// The bit order type name that we found was not what we expected ("Lsb0" or "Msb0").
	OrderFormatNotSupported(String),
}

impl core::fmt::Display for FromMetadataError {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		match self {
			FromMetadataError::OrderFormatNotFound(n) => {
				write!(f, "Bit order type {n} not found in registry")
			}
			FromMetadataError::StoreFormatNotFound(n) => {
				write!(f, "Bit store type {n} not found in registry")
			}
			FromMetadataError::NoBitOrderIdent => {
				write!(f, "Bit order cannot be identified")
			}
			FromMetadataError::StoreFormatNotSupported(s) => {
				write!(f, "Bit store type '{s}' is not supported")
			}
			FromMetadataError::OrderFormatNotSupported(s) => {
				write!(f, "Bit order type '{s}' is not supported")
			}
		}
	}
}

#[cfg(feature = "std")]
impl std::error::Error for FromMetadataError {}

#[cfg(feature = "scale-info")]
#[cfg(test)]
mod test {
	use super::*;

	fn make_type<T: scale_info::TypeInfo + 'static>() -> (u32, scale_info::PortableRegistry) {
		let m = scale_info::MetaType::new::<T>();
		let mut types = scale_info::Registry::new();
		let id = types.register_type(&m);
		let portable_registry: scale_info::PortableRegistry = types.into();

		(id.id, portable_registry)
	}

	fn assert_format<T: scale_info::TypeInfo + 'static>(store: StoreFormat, order: OrderFormat) {
		// Encode to metadata:
		let (id, types) = make_type::<T>();

		// Pull out said type info:
		let ty = match &types.resolve(id).unwrap().type_def {
			scale_info::TypeDef::BitSequence(b) => b,
			_ => panic!("expected type to look like a bit sequence"),
		};

		// We should be able to obtain a valid Format from it:
		let actual_format =
			crate::Format::from_metadata(ty, &types).expect("can obtain BitSeq Format from type");

		// The format should match the one we expect:
		assert_eq!(Format::new(store, order), actual_format);
	}

	#[test]
	fn format_extracted_properly() {
		use bitvec::{
			order::{Lsb0, Msb0},
			vec::BitVec,
		};

		assert_format::<crate::Bits>(StoreFormat::U8, OrderFormat::Lsb0);

		assert_format::<BitVec<u8, Lsb0>>(StoreFormat::U8, OrderFormat::Lsb0);
		assert_format::<BitVec<u16, Lsb0>>(StoreFormat::U16, OrderFormat::Lsb0);
		assert_format::<BitVec<u32, Lsb0>>(StoreFormat::U32, OrderFormat::Lsb0);
		assert_format::<BitVec<u64, Lsb0>>(StoreFormat::U64, OrderFormat::Lsb0);
		assert_format::<BitVec<u8, Msb0>>(StoreFormat::U8, OrderFormat::Msb0);
		assert_format::<BitVec<u16, Msb0>>(StoreFormat::U16, OrderFormat::Msb0);
		assert_format::<BitVec<u32, Msb0>>(StoreFormat::U32, OrderFormat::Msb0);
		assert_format::<BitVec<u64, Msb0>>(StoreFormat::U64, OrderFormat::Msb0);
	}
}
