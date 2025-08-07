# memapi changelog

_no versions before 0.13.2 have a changelog as I started the changelog in that version and haven't yet backtracked._

## Table of Contents

- [Version 0.16.0 Predicted](#version-0160-predicted)
- [Version 0.15.0](#version-0150)
  - [Commit 4](#commit-4-2025-8-05)
  - [Commit 3](#commit-3-2025-8-05)
  - [Commit 2](#commit-2-2025-8-05)
  - [Commit 1](#commit-1-2025-8-05)
- [Version 0.14.3](#version-0143-2025-8-05)
  - [Commit 2](#commit-2-2025-8-04)
  - [Commit 1](#commit-1-2025-8-04)
- [Version 0.14.2](#version-0142-2025-8-03)
  - [Commit 2](#commit-2-2025-8-03)
  - [Commit 1](#commit-1-2025-8-03)
- [Version 0.14.1](#version-0141-2025-8-01)
- [Version 0.14.0](#version-0140-not-published-to-cratesio-skipping-to-0141-for-users)
  - [Commit 3 (2025-7-27)](#commit-3-2025-7-27)
  - [Commit 2 (2025-7-26)](#commit-2-2025-7-26)
  - [Commit 1 (2025-7-26)](#commit-1-2025-7-26)
- [Version 0.13.2](#version-0132-2025-7-25)

## Version 0.16.0 [Predicted]

- Debloat the primary surfaces
- Implement TODOs
- Proper tests for many untested methods and features (maybe)
- Proper benchmarks (maybe)
- Finish filling API holes in `AllocSlice`
- Performance and binary size improvements
  - make as many sections as possible `const` [perf]
  - reduce inlining [size]
  - use helpers for repetitive code [size]
- Split AllocSlice/AllocExt into multiple traits (only in consideration)

## Version 0.15.0

### Commit 7 (2025-8-06)

- Inline lib.rs
- Small fixes

### Commit 6 (2025-8-05)

- Inline alloc_ext.rs, resize_in_place.rs, and helpers.rs

### Commit 5 (2025-8-05)

- Inline jemalloc.rs and mimalloc.rs
- Removed their `#[cfg_attr(miri, track_caller)]` statements since miri doesn't support external allocators
- Fix error.rs small mistake, start working on error context

### Commit 4 (2025-8-05)

- Inline error.rs, external_alloc/mod.rs, and type_props.rs
- Generally improve type_props

### Commit 3 (2025-8-05)

- Inline unstable.rs

### Commit 2 (2025-8-05)

- Remove all `#[inline]` statements
  - i'm starting from scratch with inlining, as 182/298 functions in this project were inlined, far too many
  - next commits will all be selectively re-adding inline attributes to functions by-file

### Commit 1 (2025-8-05)

- Remove `owned` module entirely
  - it became impossible to maintain, had many bugs and other flaws, was basically the same as stdlib's Vec, and,
    honestly, it only existed because of scope creep.
- Fix and improve `AllocSlice`/`AllocExt` methods
- Add `extend_slice_from_ref`, `extend_slice` and `extend_raw_slice` to `AllocSlice`
- Make `libc` only use `std` if `std` feature is enabled
- Rename `AllocError::LayoutError` to `InvalidLayout`
- Switch to `<*mut T>::cast` instead of `as` where reasonable
- Try to deduplicate code
- Fix `stats` MSRV to match crate
- Finish some docs (crate and `SliceAllocGuard`'s)

## Version 0.14.3 (2025-8-05)

### Commit 2 (2025-8-04)

- Finish `try_init_next_slice[_grow]`/`init_next_slice_unchecked` methods in `OwnedBuf`
- Specialize `OwnedBuf`'s `clone` and improve `clone_into`
- Start adding missing tests
  - no missing docs added
  - many tests are still missing

### Commit 1 (2025-8-04)
Mostly just to transfer work done on one computer to another, minimal work done.

- Switched `OwnedBuf` methods that took another owned buffer as a "slice" to take an actual slice (and for some, an 
  allocator)
- Start adding `try_init_next_slice[_grow]`/`init_next_slice_unchecked` methods to `OwnedBuf` (parallel to
  `Vec::extend_from_slice`)
- Improve `clone_into` underlying specialization implementation
  - Still janky, using `try_insert_slice_grow` until the methods mentioned above are implemented

## Version 0.14.2 (2025-8-03)

### Commit 2 (2025-8-03)

- Switch to `libc` for c types to reduce dependencies
- Switch to fork of jemalloc and mimalloc which fixes some issues
  - now Jemalloc has a lower MSRV
  - now jemalloc can be in the Cargo.toml without breaking everything on rust versions older than 1.61
- Finish lowering MSRV to 1.56 using `const_if!` macro
- Add features which bind to jemalloc and mimalloc's features
- Pray I didn't break anything

### Commit 1 (2025-8-03)

- Rename `extra_const` to `extra_extra_const`
- Start lowering MSRV to 1.56 using `const_if!` macro
- Do stuff which was undone in the next commit with jemalloc and mimalloc

### Version 0.14.1 (2025-8-01)

- Fix MSRV as best as I can (1.63.0 → 1.61.0)
  - some stuff may unnecessarily support older versions
- Add remaining docs to AllocSlice
- Add `extra_const` feature which makes some more methods `const` at the cost of raising the MSRV (1.61.0 -→ 1.83.0)
- Remove `v1_61` feature
- Generally improve feature configuration

## Version 0.14.0 [Not published to crates.io, skipping to 0.14.1 for users]

### Commit 3 (2025-7-27)

- Add missing docs for most `AllocSlice` methods (two left)
- Fix README mistake
- Fix MSRV a bit (1.36 → 1.63?)
    - requires the v1_63 feature to be enabled, which makes a few helpers non-const
    - it's not my fault, okay? cargo is inconsistent. clippy says the msrv is fine, but then you go to compile with the
      actual msrv, and it fails

### Commit 2 (2025-7-26)

- Add missing `#![allow(missing_docs)]` to `alloc_slice` module to allow compilation before docs are added

### Commit 1 (2025-7-26)

- Lowered MSRV from 1.40 to 1.36
- Switched to `cty` crate for all C types
- Fixed `AllocExt::alloc_clone_to` variant used when the `clone_to_uninit` feature is enabled but `metadata` isn't
- Started filling API holes in `AllocSlice` (grow/realloc with a predicate, initialization function, or defaulting)
  - docs are missing
- Added `set_init` to `helpers::AllocSliceGuard` to set the initialized element count for use with partially initialized
  data
- Added `USIZE_MAX_NO_HIGH_BIT` to `type_props` to avoid repetition

## Version 0.13.2 (2025-7-25)

- Started changelog
- Lowered MSRV from 1.56 to 1.40
