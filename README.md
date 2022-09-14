# scale-bits &middot; [![CI Status][ci-badge]][ci] [![Latest Version on Crates.io][crates-badge]][crates] [![Released API docs][docs-badge]][docs]

This crate provides the `Bits` type; a drop-in, SCALE-compatible replacement for `BitVec<u8, Lsb0>` which can also be encoded-to and decoded-from various store and order types at runtime (`Lsb0` and `Msb0` orderings, and `u8`, `u16` and `u32` store types), allowing for dynamic encoding and decoding based on `scale-info` metadata.

[ci]: https://github.com/paritytech/scale-bits/actions?query=workflow%3ARust+branch%3Amaster
[ci-badge]: https://github.com/paritytech/scale-bits/workflows/Rust/badge.svg
[crates]: https://crates.io/crates/scale-bits
[crates-badge]: https://img.shields.io/crates/v/scale-bits.svg
[docs]: https://docs.rs/scale-bits
[docs-badge]: https://docs.rs/scale-bits/badge.svg