//! This module exposes a [`Bits`] type, which is a small, simple bit store
//! which is SCALE compatible with `BitVec<u8, Lsb0>`.

#[macro_use]
mod bits;
#[cfg(feature = "serde")]
mod serde;

pub use bits::{Bits, BitsIntoIter, BitsIter};
