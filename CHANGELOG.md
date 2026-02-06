# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.9.2+zsl-hard-error] - 2026-02-06

### Changed

- `Dealloc` traits' fallible functions now treat zero-sized layouts and dangling pointers as a hard
  error
- `Dealloc` traits' fallible functions are now a noop for ZSLs and dangling pointers
- All other allocation functions now treat ZSLs as an error.

## [0.9.2] - 2026-02-03

### Fixed

- `StackAlloc` catching unwinds if `catch_unwind` feature is enabled even if the `C-unwind` ABI is
  available

## [0.9.1] - 2026-02-03

### Added

- Generic `Error` type in all allocation traits

### Fixed

- crates.io build failing due to lack of stdbool.h header

## [0.9.0] - 2026-02-01

### Added

- `AllocMut`, `DeallocMut`, `GrowMut`, `ShrinkMut`, and `ReallocMut` traits behind
  `alloc_mut_traits` for allocation operations requiring mutable access to the allocator
- `AllocTemp` trait for short-lived, scoped allocations behind `alloc_temp_trait`
- `Dealloc::try_dealloc` and `DeallocMut::try_dealloc_mut` for fallible deallocation operations
- `StackAlloc` scoped allocator based on C's `alloca` behind `stack_alloc` feature
- `Layout::is_zero_sized` and `Layout::is_nonzero_sized` convenience methods
- Support for `no_std::no_alloc` environments behind `no_alloc` feature
- README.md and this CHANGELOG.md

### Changed

- Renamed `round_up_checked` helper to `align_up_checked` to better reflect its purpose
- Renamed `c_alloc::ffi::aligned_zalloc` to `c_zalloc`

### Fixed

- `CAlloc` deallocation behavior with zero-sized layouts
- `CAlloc` rounding up layout size for compatibility before checking for a zero-sized request

### Removed

- `alloc_then` helper
- `usize_bit` helper
- `check_ptr_overlap` helper
- `zsl_check` helper
- `ZeroSizedLayout(NonNull<u8>)` error in favor of just returning a dangling pointer

## [0.8.1] - 2026-01-21

### Added

- `CAlloc` for allocation with C's `aligned_alloc`
- `Layout::to_aligned_alloc_compatible` for rounding a layout to be compatible with `aligned_alloc`
- `Layout::aligned_alloc_compatible_from_size_align` for creating an `aligned_alloc` compatible
  layout in one call
- `Cause::CRoundUp` variant for failures when rounding a layout to be compatible with
  `aligned_alloc`
- `Error::Other` variant for generic string errors
- `Layout::align_to_multiple_of` method
- `is_multiple_of` const helper with lower MSRV than `<int>::is_multiple_of`
- `VarSizedStruct` trait primarily to act as a guide for implementing `VarSized` for structs with an
  unsized tail

### Changed

- Moved `type_props::USIZE_HIGH_BIT`, `type_props::USIZE_MAX_NO_HIGH_BIT`, `type_props::usize_bit`,
  `type_props::varsized_dangling_nonnull`, `type_props::varsized_dangling_ptr`,
  `type_props::varsized_nonnull_from_parts`, `type_props::varsized_ptr_from_parts`, and
  `type_props::varsized_ptr_from_parts_mut` to `helpers` module
- Renamed `AllocError` to `Error`
- Renamed `align_up_unchecked` to `align_up` and make it safe, rename `align_up` to
  `align_up_checked`
- Made nightly support automatic if a nightly compiler is detected

### Fixed

- layout tests failing due to a too-large alignment
- `Layout::padding_needed_for` returning `usize::MAX` instead of an error if `align` argument is not
  a power of two
- Some `Layout` functions performing size checks on unnecessary values

### Removed

- `RepeatLayoutError` error enum
- `layout_extend` helper in favor of `Layout::extend` method
- `ArithErr::TooLargeRhs` variant
