# Changelog

The format is based on [Keep a Changelog].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/

## 0.3.0

## Changes

- Hide the inner `Decoder` enum variants so that we have the opportunity to improve performance on them in the future with a non breaking change.

## 0.2.0

This release rewrites most of the interface and clearly differentiates between the two core offerings; a lightweight Bits type and a set of utility functions for working with SCALE encoded bits.

## 0.1.1

Initial release + clippy/doc fixes.