# Changelog

The format is based on [Keep a Changelog].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/

## 0.7.0

This release removes the `std feature` from the this crate which means that the crate is now `no_std` compatible by default.

### Changes
- Remove std feature and make fully no_std 
- Update to `scale-info` to 2.11.5

## 0.6.0

Update `scale-type-resolver` dependency to 0.2.0.

## 0.5.0

Depend on `scale-type-resolver` for a order and store enums, and remove `Format::from_metadata` (this is now available as `scale_type_resolver::portable_registry::bits_from_metadata()`).

## 0.4.0

`no_std` is now supported; use `--no-default-features` to disable "std" (`serde` and `scale-info` features both support this too).

### Changes

- Add no_std compatibility ([#2](https://github.com/paritytech/scale-bits/pull/2)). Thankyou @haerdib!

## 0.3.0

### Changes

- Hide the inner `Decoder` enum variants so that we have the opportunity to improve performance on them in the future with a non breaking change.

## 0.2.0

This release rewrites most of the interface and clearly differentiates between the two core offerings; a lightweight Bits type and a set of utility functions for working with SCALE encoded bits.

## 0.1.1

Initial release + clippy/doc fixes.