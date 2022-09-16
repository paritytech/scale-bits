# scale-bits &middot; [![CI Status][ci-badge]][ci] [![Latest Version on Crates.io][crates-badge]][crates] [![Released API docs][docs-badge]][docs]

This small utility crate provides two separate things:

1. A `Bits` type that can be SCALE encoded and decoded, and is fully
   SCALE compatible with a `BitVec<u8, Lsb0>`. It's a deliberately simple
   type that is conceptually just a sequence of bools, and can be used as
   a replacement for `BitVec` when you don't need the additional complexity
   and functionality that it comes with. See the `bits` module for more.
2. Utility methods to help encode and decode arbitrary bit sequences from their
   SCALE representation, or skip over the corresponding bytes entirely, with zero
   allocations. These bypass the need to first go via some `BitVec` with the
   right store/order type, and are WASM compatible (unlike `BitVec`'s `u64` store
   type). See the `scale` module for more.

These things play nicely together (ie you can encode and decode arbitrary bit
sequences directly into the `Bits` type), but don't need to be used together.

[ci]: https://github.com/paritytech/scale-bits/actions?query=workflow%3ARust+branch%3Amaster
[ci-badge]: https://github.com/paritytech/scale-bits/workflows/Rust/badge.svg
[crates]: https://crates.io/crates/scale-bits
[crates-badge]: https://img.shields.io/crates/v/scale-bits.svg
[docs]: https://docs.rs/scale-bits
[docs-badge]: https://docs.rs/scale-bits/badge.svg