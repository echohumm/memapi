# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres
to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

[//]: # (methinks 1.0.0 soon? maybe im getting ahead of myself though)

## [0.12.1] - 2026-08-30

### Changed

* Updated `README.md`

---

## [0.12.0] - 2026-08-30

### Added

* `Error::ReallocSmallerAlign` for when attempting to reallocate with a smaller new alignment
* `PtrProps::varsized_metadata` for getting the size of `VarSized` types
* `alloc_checked_trait` feature controlling `traits::alloc_checked` module
* `traits::AllocDescriptor::FEATURES` supported feature bitflags with `traits::AllocFeatures`
* `helpers::udouble`
* `ArithOp::DivCeil` and the matching checked arithmetic operation
* `traits::zst_alloc::{ZstAlloc, ZstDealloc, ZstRealloc, ZstBasicAlloc, ZstFullAlloc}`, a stateless allocator trait
  family for allocators with no per-instance state, exposing associated functions instead of `&self` methods;
  implemented for `CAlloc`, `DefaultAlloc`, and `alloc::alloc::Global`
* `traits::zst_alloc_temp::ZstAllocTemp`, the stateless counterpart to `AllocTemp`, behind the `alloc_temp_trait`
  feature; implemented for `allocs::stack_alloc::StackAlloc` and all types which implement
  `traits::zst_alloc::ZstDealloc`
* `traits::data::type_props::KnownAlign` trait, unifying the alignment constant across `Sized`, `VarSized`, and
  `VarSizedStruct` types
* `AllocDescriptor::MIN_ALIGN`, the minimum alignment guaranteed by an allocator (defaults to `1`)
* `AllocDescriptor::supports`, a default method for checking whether an allocator supports a given `AllocFeatures` set
* `helpers::void_ptr` type alias for a `*mut c_void`, and `helpers::is_aligned` to check if a pointer meets an alignment
* `full_std` and `full_nightly_std` feature bundles

### Changed

* `Dealloc::try_dealloc` on a zero-sized layout or dangling pointer is now a no-op, not an error
* Renamed `Layout::is_zero_sized` to `Layout::is_zsl`
* Renamed `traits::AllocError` to `AllocDescriptor`
* Renamed `Error::InvalidLayout` to `LayoutErr`; removed size and align fields
* `Layout` functions' error type is now `LayoutErr`
* `LayoutErr` now stores relevant data for layout errors
* Moved `VarSized` pointer creation functions from `helpers` to `traits::data::type_props`
* Renamed `dev` feature to `__dev`
* `Dealloc::checked_dealloc` moved to `alloc_checked::alloc::CheckedDealloc::checked_dealloc`
* `Realloc`/`ReallocMut` (and their checked counterparts) now handle both growing and shrinking through a single
  `realloc`/`rezalloc` call instead of separate `Grow`/`Shrink` traits
* `AllocTemp` now requires `AllocDescriptor` as a supertrait instead of declaring its own `Error` associated type
* `AllocFeatures` is now backed by `u16` instead of `u8` for future extensions
* `full` feature bundle now bundles `c_alloc`, `alloc_checked_trait`, and `stack_alloc`; `os_err_reporting` and
  `catch_unwind` moved into the new `full_std` bundle
* `Layout::extend`, `Layout::repeat`, and `Layout::repeat_packed` are now unconditionally `const fn`
* Reallocation now skips deallocating the old block if the allocator doesn't report `AllocFeatures::DEALLOC` support,
  instead of always attempting (and potentially erroring on) deallocation

### Fixed

* Reallocation that requests a smaller alignment is now treated as an error (`Error::ReallocSmallerAlign`) instead of
  allowing potential undefined behavior
* Build spuriously failing on MSRV
* `CAlloc` allocations being unaligned in certain cases

### Removed

* Useless `sized_hierarchy` feature
* Useless `all_nightly` feature bundle with only one item
* `c_str` feature in favor of auto-detecting a compatible compiler version
* `full_msrv` feature made useless by removing `c_str`
* `Error::DanglingDeallocation` error; attempting to deallocate a dangling pointer is now a no-op.
* `Error::ZeroSizedLayout` error
* `helpers::align_up_checked`
* `helpers::dangling_nonnull`; replaced by `SizedProps::DANGLING_PTR` and `Layout::dangling`
* `traits::data::marker::{Thin,SizeMeta}`
* `helpers::{AllocGuard, SliceAllocGuard}`
* `GlobalAlloc` implementation for `DefaultAlloc`
* `Grow`, `Shrink`, `GrowMut`, `ShrinkMut` traits, and their checked counterparts `CheckedGrow`, `CheckedShrink`,
  `CheckedGrowMut`, `CheckedShrinkMut`; growing and shrinking are now both handled through `Realloc`/ `ReallocMut`/
  `CheckedRealloc`/`CheckedReallocMut`
* `Error::GrowSmallerNewLayout` and `Error::ShrinkLargerNewLayout`
* `Error::CaughtUnwind` (the pre-1.71 `catch_unwind` failure case now returns `Error::Other`)
* `AllocFeatures::GROW`, `AllocFeatures::SHRINK`, `AllocFeatures::CHECKED_GROW`, `AllocFeatures::CHECKED_SHRINK` in
  favor of `AllocFeatures::REALLOC` and `AllocFeatures::CHECKED_REALLOC`
* `ffi::c_alloc::MIN_ALIGN` (superseded by `AllocDescriptor::MIN_ALIGN`, exposed as `CAlloc::MIN_ALIGN`)
* `SizedProps::ALN`, `VarSized::ALN`, `VarSizedStruct::ALN` (superseded by `KnownAlign::ALN`)
* `helpers::checked_op` (inlined at call sites for performance)

---

## [0.11.3] - 2026-02-15

### Fixed

* Crate failing to compile on Windows with the `c_alloc` feature

* Crate failing to compile on Apple systems with the `c_alloc` feature

---

## [0.11.2] - 2026-02-15

### Added

* `ffi::c_alloc::MIN_ALIGN`, the current platform's minimum guaranteed alignment returned by implicitly aligned
  allocation functions

### Changed

* `CAlloc` now uses `malloc`/`calloc` when possible instead of explicitly aligned allocation functions

### Fixed

* Crate failing to compile on Windows with the `c_alloc` feature
* Return code of `posix_memalign` being discarded

---

## [0.11.1] - 2026-02-14

### Changed

* Switch `CAlloc` from using `aligned_alloc` on unix to `posix_memalign`

---

## [0.11.0] - 2026-02-14

### Changed

* Rename shared `AllocErrorType` trait to `AllocError`
* Remove most public re-exports and non-modules from the main crate in favor of a `prelude` module
* `no_alloc` feature now just switches to using the `std` crate if both features are enabled

---

## [0.10.0] - 2026-02-11

### Added

* `AllocErrorType` trait shared between `alloc_mut` and `alloc` traits
* `Error::Unsupported` variant for unsupported operations

### Changed

* Minimize main crate surface
* Remove `alloc_mut_traits` feature, make `alloc_mut` traits required

---

## [0.9.4] - 2026-02-06

### Changed

* `Dealloc` traits' fallible functions now treat zero-sized layouts and dangling pointers as a hard error
* `Dealloc` traits' fallible functions are now a noop for ZSLs and dangling pointers
* All other allocation functions now treat ZSLs as an error

### Added

* Added `Layout::array_unchecked` constructor

---

## [0.9.2] - 2026-02-03

### Fixed

* `StackAlloc` catching unwinds if `catch_unwind` feature is enabled even if the `C-unwind` ABI is available

---

## [0.9.1] - 2026-02-03

### Added

* Generic `Error` type in all allocation traits

### Fixed

* crates.io build failing due to lack of stdbool.h header

---

## [0.9.0] - 2026-02-01

### Added

* `AllocMut`, `DeallocMut`, `GrowMut`, `ShrinkMut`, and `ReallocMut` traits behind
  `alloc_mut_traits` for allocation operations requiring mutable access to the allocator
* `AllocTemp` trait for short-lived, scoped allocations behind `alloc_temp_trait`
* `Dealloc::try_dealloc` and `DeallocMut::try_dealloc_mut` for fallible deallocation operations
* `StackAlloc` scoped allocator based on C's `alloca` behind `stack_alloc` feature
* `Layout::is_zero_sized` and `Layout::is_nonzero_sized` convenience methods
* Support for `no_std::no_alloc` environments behind `no_alloc` feature
* README.md and this CHANGELOG.md

### Changed

* Renamed `round_up_checked` helper to `align_up_checked` to better reflect its purpose
* Renamed `c_alloc::ffi::aligned_zalloc` to `c_zalloc`

### Fixed

* `CAlloc` deallocation behavior with zero-sized layouts
* `CAlloc` rounding up layout size for compatibility before checking for a zero-sized request

### Removed

* `alloc_then` helper
* `usize_bit` helper
* `check_ptr_overlap` helper
* `zsl_check` helper
* `ZeroSizedLayout(NonNull<u8>)` error in favor of just returning a dangling pointer

---

## [0.8.1] - 2026-01-21

### Added

* `CAlloc` for allocation with C's `aligned_alloc`
* `Layout::to_aligned_alloc_compatible` for rounding a layout to be compatible with `aligned_alloc`
* `Layout::aligned_alloc_compatible_from_size_align` for creating an `aligned_alloc` compatible layout in one call
* `Cause::CRoundUp` variant for failures when rounding a layout to be compatible with
  `aligned_alloc`
* `Error::Other` variant for generic string errors
* `Layout::align_to_multiple_of` method
* `is_multiple_of` const helper with lower MSRV than `<int>::is_multiple_of`
* `VarSizedStruct` trait primarily to act as a guide for implementing `VarSized` for structs with an unsized tail

### Changed

* Moved `type_props::USIZE_HIGH_BIT`, `type_props::USIZE_MAX_NO_HIGH_BIT`, `type_props::usize_bit`,
  `type_props::varsized_dangling_nonnull`, `type_props::varsized_dangling_ptr`,
  `type_props::varsized_nonnull_from_parts`, `type_props::varsized_ptr_from_parts`, and
  `type_props::varsized_ptr_from_parts_mut` to `helpers` module
* Renamed `AllocError` to `Error`
* Renamed `align_up_unchecked` to `align_up` and make it safe, rename `align_up` to
  `align_up_checked`
* Made nightly support automatic if a nightly compiler is detected

### Fixed

* layout tests failing due to a too-large alignment
* `Layout::padding_needed_for` returning `usize::MAX` instead of an error if `align` argument is not a power of two
* Some `Layout` functions performing size checks on unnecessary values

### Removed

* `RepeatLayoutError` error enum
* `layout_extend` helper in favor of `Layout::extend` method
* `ArithErr::TooLargeRhs` variant
