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

use super::Bits;
use serde::{
	de::{self, Deserializer, Visitor},
	ser::SerializeSeq,
	Deserialize, Serialize, Serializer,
};

impl Serialize for Bits {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut seq = serializer.serialize_seq(Some(self.len()))?;
		for b in self.iter() {
			seq.serialize_element(&b)?;
		}
		seq.end()
	}
}

impl<'de> Deserialize<'de> for Bits {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		struct BitsVisitor;

		impl<'de> Visitor<'de> for BitsVisitor {
			type Value = Bits;

			fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
				formatter.write_str("a sequence of booleans")
			}

			fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
			where
				A: de::SeqAccess<'de>,
			{
				let prealloc_len = seq.size_hint().unwrap_or(0);
				let mut bits = Bits::with_capacity(prealloc_len);
				while let Some(b) = seq.next_element()? {
					bits.push(b);
				}
				Ok(bits)
			}
		}

		deserializer.deserialize_seq(BitsVisitor)
	}
}

#[cfg(test)]
mod test {
	use crate::bits::Bits;
	use alloc::vec;

	#[test]
	fn ser_deser_bits() {
		let checks =
			vec![(bits![], "[]"), (bits![true], "[true]"), (bits![false, true], "[false,true]")];

		for (bits, json) in checks {
			// test serializing.
			assert_eq!(serde_json::to_string(&bits).unwrap(), json);
			// test deserializing:
			assert_eq!(serde_json::from_str::<Bits>(json).unwrap(), bits);
		}
	}
}
