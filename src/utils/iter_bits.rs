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

// Iterating over the bits starting with the lsb or msb.

macro_rules! iter_bits_msb0 {
    ($byte:ident; $bits:expr) => {{
        let mut shift = $bits - 1;
        let mut done = false;
        std::iter::from_fn(move || {
            if done {
                return None
            }

            let res = match ($byte >> shift) & 0b1 {
                1 => true,
                0 => false,
                _ => unreachable!()
            };

            if shift == 0 {
                done = true
            } else {
                shift -= 1
            }

            Some(res)
        })
    }}
}

macro_rules! iter_bits_lsb0 {
    ($byte:ident; $bits:expr) => {{
        let mut shift = 0;
        std::iter::from_fn(move || {
            if shift == $bits {
                return None
            }

            let res = match ($byte >> shift) & 0b1 {
                1 => true,
                0 => false,
                _ => unreachable!()
            };

            shift += 1;

            Some(res)
        })
    }}
}

pub(crate) fn iter_u8_msb0(byte: u8) -> impl Iterator<Item = bool> {
    iter_bits_msb0!(byte; 8)
}

pub(crate) fn iter_u16_msb0(byte: u16) -> impl Iterator<Item = bool> {
    iter_bits_msb0!(byte; 16)
}
pub(crate) fn iter_u16_lsb0(byte: u16) -> impl Iterator<Item = bool> {
    iter_bits_lsb0!(byte; 16)
}

pub(crate) fn iter_u32_msb0(byte: u32) -> impl Iterator<Item = bool> {
    iter_bits_msb0!(byte; 32)
}
pub(crate) fn iter_u32_lsb0(byte: u32) -> impl Iterator<Item = bool> {
    iter_bits_lsb0!(byte; 32)
}

#[cfg(test)]
mod test {
    use super::*;

    const I: bool = true;
    const O: bool = false;

    #[test]
    fn test_iter_bits() {

        fn v<I: Iterator<Item=bool>>(i: I) -> Vec<bool> {
            i.collect()
        }

        assert_eq!(v(iter_u8_msb0(0)), vec![O,O,O,O,O,O,O,O]);

        assert_eq!(v(iter_u8_msb0(0b00101101)), vec![O,O,I,O,I,I,O,I]);

        assert_eq!(v(iter_u16_lsb0(0b0000111100101101)), vec![I,O,I,I,O,I,O,O,I,I,I,I,O,O,O,O]);
        assert_eq!(v(iter_u16_msb0(0b0000111100101101)), vec![O,O,O,O,I,I,I,I,O,O,I,O,I,I,O,I]);

        assert_eq!(v(iter_u32_lsb0(0b0000111100101101_0000111100101101)), vec![I,O,I,I,O,I,O,O,I,I,I,I,O,O,O,O,I,O,I,I,O,I,O,O,I,I,I,I,O,O,O,O]);
        assert_eq!(v(iter_u32_msb0(0b0000111100101101_0000111100101101)), vec![O,O,O,O,I,I,I,I,O,O,I,O,I,I,O,I,O,O,O,O,I,I,I,I,O,O,I,O,I,I,O,I]);
    }

}