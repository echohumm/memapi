# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- Generic `Error` type in all allocation traits

## [0.9.0] - 2026-02-02

### Added

- `AllocMut`, `DeallocMut`, `GrowMut`, `ShrinkMut`, and `ReallocMut` traits behind
  `alloc_mut_traits` for allocation operations requiring mutable access to the allocator
- `AllocTemp` trait for short-lived, scoped allocations behind `alloc_temp_trait`
- `Dealloc::try_dealloc` and `DeallocMut::try_dealloc_mut` for fallible deallocation operations
- `StackAlloc` scoped allocator based on C's `alloca` behind `stack_alloc` feature
- `Layout::is_zero_sized` and `Layout::is_nonzero_sized` convenience methods
- Support for `no_std::no_alloc` environments behind `no_alloc` feature
- README.md and this CHANGELOG.md

### Removed

- `alloc_then` helper
- `usize_bit` helper
- `check_ptr_overlap` helper
- `zsl_check` helper
- `ZeroSizedLayout(NonNull<u8>)` error in favor of just returning a dangling pointer

### Changed

- Renamed `round_up_checked` helper to `align_up_checked` to better reflect its purpose
- Renamed `c_alloc::ffi::aligned_zalloc` to `c_zalloc`

### Fixed

- `CAlloc` deallocation behavior with zero-sized layouts
- `CAlloc` rounding up layout size for compatibility before checking for a zero-sized request
