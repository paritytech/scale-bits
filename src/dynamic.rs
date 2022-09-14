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

//! Ths module allows [`Bits`] to be dynamically encoded and decoded into/from a given
//! [`Format`]. The [`Format`] can either be provided manually, or extracted from
//! [`scale_info`] type information.

use scale_info::{
    TypeDef,
    TypeDefBitSequence,
    TypeDefPrimitive,
    form::PortableForm,
    PortableRegistry,
};
use codec::{
    Compact,
    Decode,
    Encode,
    Error as CodecError,
};
use crate::Bits;
use crate::utils::iter_bits::{
    iter_u16_lsb0,
    iter_u16_msb0,
    iter_u32_lsb0,
    iter_u32_msb0,
    iter_u8_msb0,
};
use crate::utils::iter_from_bits::{
    iter_bits_to_u16_lsb,
    iter_bits_to_u16_msb,
    iter_bits_to_u32_lsb,
    iter_bits_to_u32_msb,
    iter_bits_to_u8_msb,
};

/// A description of a format to encode/decode [`Bits`] to/from.
pub struct Format {
    store: StoreType,
    order: OrderType
}

impl Format {
    /// Define a new format by providing a store and order.
    ///
    /// # Example
    ///
    /// ```rust
    /// use scale_bits::dynamic::{ Format, StoreType, OrderType };
    ///
    /// let format = Format::new(StoreType::U8, OrderType::Lsb0);
    /// ```
    pub fn new(store: StoreType, order: OrderType) -> Self {
        Format { store, order }
    }
    /// Use metadata to obtain details about the format.
    pub fn from_metadata(
        ty: &TypeDefBitSequence<PortableForm>,
        types: &PortableRegistry,
    ) -> Result<Format, BitsDetailsError> {
        let bit_store_ty = ty.bit_store_type().id();
        let bit_order_ty = ty.bit_order_type().id();

        // What is the backing store type expected?
        let bit_store_def = types
            .resolve(bit_store_ty)
            .ok_or(BitsDetailsError::StoreTypeNotFound(bit_store_ty))?
            .type_def();

        // What is the bit order type expected?
        let bit_order_def = types
            .resolve(bit_order_ty)
            .ok_or(BitsDetailsError::OrderTypeNotFound(bit_order_ty))?
            .path()
            .ident()
            .ok_or(BitsDetailsError::NoBitOrderIdent)?;

        let bit_store_out = match bit_store_def {
            TypeDef::Primitive(TypeDefPrimitive::U8) => Some(StoreType::U8),
            TypeDef::Primitive(TypeDefPrimitive::U16) => Some(StoreType::U16),
            TypeDef::Primitive(TypeDefPrimitive::U32) => Some(StoreType::U32),
            // TypeDef::Primitive(TypeDefPrimitive::U64) => Some(BitStoreTy::U64),
            _ => None,
        }
        .ok_or_else(|| BitsDetailsError::StoreTypeNotSupported(format!("{bit_store_def:?}")))?;

        let bit_order_out = match &*bit_order_def {
            "Lsb0" => Some(OrderType::Lsb0),
            "Msb0" => Some(OrderType::Msb0),
            _ => None,
        }
        .ok_or(BitsDetailsError::OrderTypeNotSupported(bit_order_def))?;

        Ok(Format { store: bit_store_out, order: bit_order_out })
    }

    /// Given some number of bits, how many bytes, in total, would it take to encode that number of
    /// bits given the specified format.
    ///
    /// # Example
    ///
    /// ```rust
    /// use scale_bits::{ Bits, bits, dynamic::{ Format, StoreType, OrderType } };
    ///
    /// let bits = bits![1,0,1,1,0,1,0,1,0,0,1];
    /// let format = Format::new(StoreType::U8, OrderType::Lsb0);
    ///
    /// // Encode bits with a given format:
    /// let mut out = vec![];
    /// format.encode_bits_to(&bits, &mut out);
    ///
    /// // `encoded_size()` returns the same length without needing to allocate/encode:
    /// let expected_len = format.encoded_size(bits.len());
    /// assert_eq!(out.len(), expected_len);
    /// ```
    pub fn encoded_size(&self, number_of_bits: usize) -> usize {
        // How many bytes would it take to encode the number of bits (this comes first in the encoding):
        let compact_len = Compact(number_of_bits as u32).encoded_size();
        // How many bytes would be used to encode that number of bits given our store size?
        let (number_of_bytes, _) = self.store.byte_len_from_bit_len(number_of_bits);

        compact_len + number_of_bytes
    }

    /// Encode the provided [`Bits`] to the output in the given format.
    ///
    /// # Example
    ///
    /// ```rust
    /// use scale_bits::{ Bits, bits, dynamic::{ Format, StoreType, OrderType } };
    ///
    /// let bits = bits![1,0,1,1,0,1,0,1,0,0,1];
    /// let format = Format::new(StoreType::U8, OrderType::Lsb0);
    ///
    /// // SCALE encode bits into the chosen format:
    /// let mut out = vec![];
    /// format.encode_bits_to(&bits, &mut out);
    /// ```
    pub fn encode_bits_to(&self, bits: &Bits, out: &mut Vec<u8>) {
        match (self.store, self.order) {
            // The "native" format that Bits is also in, so we just use the base
            // encode impl.
            (StoreType::U8, OrderType::Lsb0) => {
                bits.encode_to(out);
            },
            // For every other impl, we iterate over the bits and push them to the output
            // in the correct format.
            (StoreType::U8, OrderType::Msb0) => {
                Compact(bits.len() as u32).encode_to(out);
                for byte in iter_bits_to_u8_msb(bits.iter()) {
                    byte.encode_to(out);
                }
            },
            (StoreType::U16, OrderType::Lsb0) => {
                Compact(bits.len() as u32).encode_to(out);
                for byte in iter_bits_to_u16_lsb(bits.iter()) {
                    byte.encode_to(out);
                }
            },
            (StoreType::U16, OrderType::Msb0) => {
                Compact(bits.len() as u32).encode_to(out);
                for byte in iter_bits_to_u16_msb(bits.iter()) {
                    byte.encode_to(out);
                }
            },
            (StoreType::U32, OrderType::Lsb0) => {
                Compact(bits.len() as u32).encode_to(out);
                for byte in iter_bits_to_u32_lsb(bits.iter()) {
                    byte.encode_to(out);
                }
            },
            (StoreType::U32, OrderType::Msb0) => {
                Compact(bits.len() as u32).encode_to(out);
                for byte in iter_bits_to_u32_msb(bits.iter()) {
                    byte.encode_to(out);
                }
            },
        }
    }

    /// Decode the provided bytes into [`Bits`] assuming the given format.
    ///
    /// # Example
    ///
    /// ```rust
    /// use scale_bits::{ Bits, bits, dynamic::{ Format, StoreType, OrderType } };
    ///
    /// let bits = bits![1,0,1,1,0,1,0,1,0,0,1];
    /// let format = Format::new(StoreType::U8, OrderType::Lsb0);
    ///
    /// // SCALE encode bits into the chosen format:
    /// let mut out = vec![];
    /// format.encode_bits_to(&bits, &mut out);
    ///
    /// // Then, we can decode these back given the same format:
    /// let new_bits = format.decode_bits_from(&mut &*out).unwrap();
    ///
    /// assert_eq!(bits, new_bits);
    /// ```
    pub fn decode_bits_from(&self, bytes: &mut &[u8]) -> Result<Bits, CodecError> {
        let bits = match (self.store, self.order) {
            // The "native" format that Bits is also in, so we just use the base
            // decode impl.
            (StoreType::U8, OrderType::Lsb0) => {
                Bits::decode(bytes)?
            },
            // For every other impl, we iterate over the bits and push them to our
            // Bits struct.
            (StoreType::U8, OrderType::Msb0) => {
                let bit_len = Compact::<u32>::decode(bytes)?.0 as usize;
                let (byte_len, _) = StoreType::U8.byte_len_from_bit_len(bit_len);
                let mut bits = Bits::with_capacity(bit_len);

                for _ in 0..byte_len {
                    let byte = u8::decode(bytes)?;
                    iter_u8_msb0(byte).for_each(|b| bits.push(b));
                }

                bits
            },
            (StoreType::U16, OrderType::Lsb0) => {
                let bit_len = Compact::<u32>::decode(bytes)?.0 as usize;
                let (byte_len, _) = StoreType::U16.byte_len_from_bit_len(bit_len);
                let mut bits = Bits::with_capacity(bit_len);

                for _ in 0..byte_len {
                    let byte = u16::decode(bytes)?;
                    iter_u16_lsb0(byte).for_each(|b| bits.push(b));
                }

                bits
            },
            (StoreType::U16, OrderType::Msb0) => {
                let bit_len = Compact::<u32>::decode(bytes)?.0 as usize;
                let (byte_len, _) = StoreType::U16.byte_len_from_bit_len(bit_len);
                let mut bits = Bits::with_capacity(bit_len);

                for _ in 0..byte_len {
                    let byte = u16::decode(bytes)?;
                    iter_u16_msb0(byte).for_each(|b| bits.push(b));
                }

                bits
            },
            (StoreType::U32, OrderType::Lsb0) => {
                let bit_len = Compact::<u32>::decode(bytes)?.0 as usize;
                let (byte_len, _) = StoreType::U32.byte_len_from_bit_len(bit_len);
                let mut bits = Bits::with_capacity(bit_len);

                for _ in 0..byte_len {
                    let byte = u32::decode(bytes)?;
                    iter_u32_lsb0(byte).for_each(|b| bits.push(b));
                }

                bits
            },
            (StoreType::U32, OrderType::Msb0) => {
                let bit_len = Compact::<u32>::decode(bytes)?.0 as usize;
                let (byte_len, _) = StoreType::U32.byte_len_from_bit_len(bit_len);
                let mut bits = Bits::with_capacity(bit_len);

                for _ in 0..byte_len {
                    let byte = u32::decode(bytes)?;
                    iter_u32_msb0(byte).for_each(|b| bits.push(b));
                }

                bits
            },
        };
        Ok(bits)
    }

}

/// This is a runtime representation of the order that bits will be written
/// to the specified [`StoreType`].
///
/// - [`OrderType::Lsb0`] means that we write to the least significant bit first
///   and then work our way up to the most significant bit as we push new bits.
/// - [`OrderType::Msb0`] means that we write to the most significant bit first
///   and then work our way down to the least significant bit as we push new bits.
///
/// These are equivalent to `bitvec`'s `order::Lsb0` and `order::Msb0`.
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum OrderType {
    /// Least significant bit first.
    Lsb0,
    /// Most significant bit first.
    Msb0,
}

/// This is a runtime representation of the store type that we're targeting. These
/// are equivalent to the `bitvec` store types `u8`, `u16` and so on.
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum StoreType {
    /// Equivalent to [`u8`].
    U8,
    /// Equivalent to [`u16`].
    U16,
    /// Equivalent to [`u32`].
    U32,
}

impl StoreType {
    /// Calculate the length in bytes given a length in bits and a store type.
    /// Return a tuple of the byte length needed, and a count of the bits in the last byte.
    pub(crate) fn byte_len_from_bit_len(self, bit_len: usize) -> (usize, usize) {
        match self {
            StoreType::U8 => {
                let remainder: usize = bit_len & 0b111;
                let byte_len = bit_len / 8 + if remainder > 0 { 1 } else { 0 };
                (byte_len, remainder)
            },
            StoreType::U16 => {
                let remainder: usize = bit_len & 0b1111;
                let byte_len = bit_len / 16 + if remainder > 0 { 1 } else { 0 };
                (byte_len, remainder)
            },
            StoreType::U32 => {
                let remainder: usize = bit_len & 0b11111;
                let byte_len = bit_len / 32 + if remainder > 0 { 1 } else { 0 };
                (byte_len, remainder)
            },
        }
    }
}

/// An error that can occur when we try to encode or decode to a SCALE bit sequence type.
#[derive(Debug, Clone, thiserror::Error, PartialEq)]
pub enum BitsDetailsError {
    /// The registry did not contain the bit order type listed.
    #[error("Bit order type {0} not found in registry")]
    OrderTypeNotFound(u32),
    /// The registry did not contain the bit store type listed.
    #[error("Bit store type {0} not found in registry")]
    StoreTypeNotFound(u32),
    /// The bit order type did not have a valid identifier/name.
    #[error("Bit order cannot be identified")]
    NoBitOrderIdent,
    /// The bit store type that we found was not what we expected (a primitive u8/u16/u32/u64).
    #[error("Bit store type {0} is not supported")]
    StoreTypeNotSupported(String),
    /// The bit order type name that we found was not what we expected ("Lsb0" or "Msb0").
    #[error("Bit order type {0} is not supported")]
    OrderTypeNotSupported(String),
}