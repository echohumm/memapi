# memapi changelog

_no versions before 0.13.2 have a changelog as I started the changelog in that version and haven't yet backtracked._

## Table of Contents

- [Current low-priority to-dos](#current-low-priority-to-dos)
- [Version 0.18.0](#version-0180)
  - [Commit 5](#commit-5-2025-8-16)
  - [Commit 4](#commit-4-2025-8-16-834)
  - [Commit 3](#commit-3-2025-8-15-2341)
  - [Commit 2](#commit-2-2025-8-14-1926)
  - [Commit 1](#commit-1-2025-8-13)
- [Version 0.17.0](#version-0170-2025-8-10)
  - [Commit 2](#commit-2-2025-8-10)
  - [Commit 1](#commit-1-2025-8-09)
- [Version 0.16.0](#version-0160-2025-8-08)
- [Version 0.15.2](#version-0152-2025-8-07)
- [Version 0.15.0](#version-0150-2025-8-07)
  - [Commit 9](#commit-9-2025-8-07)
  - [Commit 8](#commit-8-2025-8-07)
  - [Commit 7](#commit-7-2025-8-06)
  - [Commit 6](#commit-6-2025-8-05)
  - [Commit 5](#commit-5-2025-8-05)
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

## Entry format

```markdown
## Version <MAJOR>.<MINOR>.<PATCH> [[<META_NOTE>] &| (<PUBLISH_DATE> <PUBLISH_MST_TIME>)]

### Commit <COMMIT_NUMBER> {on release: (<DATE> <MST_TIME>)}

- <CHANGE MESSAGE> [(<NOTE>)
  [- <SUBCHANGE_NOTE>]
```

# Current high-priority to-dos

- Sort stuff and fix module structure (it's SO bad)
- Make other external allocators' methodology consistent with Malloc's
- Split AllocSlice/AllocExt into multiple traits

## Current low-priority to-dos

- Performance and binary size improvements
  - make as many sections as possible `const` [perf]
  - use helpers for repetitive code [size] (~60% done, maybe?)
- Proper tests for many untested methods and features

## Version 0.18.0

### Commit 5 (2025-8-16)

- Update README.md
- Somewhat fix module structure
- Make MiMalloc error reporting thread-local
- Add `mimalloc_global_err` to add a global error state in addition to the new thread-local one
- Reduce `external::mimalloc`, and `external::ffi::libc` repetition
- Add tests for `Malloc`
- Small fixes and improvements

### Commit 4 (2025-8-16 8:34)

- Start working on module structure (WIP)

### Commit 3 (2025-8-15 23:41)

- Remove feature bundles
- Make compatible with `no_std::no_alloc` with `no_alloc` feature
- Add `Malloc` allocator as a wrapper around libc's allocation functions
- Remove `*ref` functions from `AllocSlice`/`AllocExt`
- Move many `AllocSlice` methods to `AllocSliceExt` (temporary, until separated into more 
  descriptive traits)
- Add `malloc_defaultalloc` feature to make `DefaultAlloc` use malloc instead of Rust's allocation 
  functions when `no_alloc` is on
- Shorten more method names (e.g., `alloc_slice` -> `salloc`, `alloc_copy_slice_to` -> `salloc_copy`)

### Commit 2 (2025-8-14 19:26)

Haven't tested this fully yet

- Slightly improve build.rs
- Improve feature bundles
- Fix README and document feature bundles in it
- Start making some error paths cold
- Remove jemalloc reallocation's same layout alignment requirement
- Move mim/jemalloc ResizeInPlace implementations to their own files
- Move features/fallible_dealloc.rs to a directory module
  - Added methods parallel to alloc_ext/alloc_slice
- Split features/stats.rs into multiple modules in a directory module
- Add `ThreadSafeIOLogger` behind `stats_thread_safe_io` feature
- (WIP) Generally clean up docs, modules, etc.
  - still a lot to do
  - also made some backwards progress (my brain was dying after doing features/fallible_dealloc/ext.rs, that file is 
    seriously a cognitohazard for no reason. just thinking about it fogs my brain.)
- Add AllocSlice missing unchecked variants

### Commit 1 (2025-8-13)

- Add `AllocAlignedAt` trait under `alloc_aligned_at` feature
- Add `dev` feature which unhides several internal functions used in implementations.
- Rename `FallibleDealloc` to `DeallocChecked`
- Rename and improve feature bundles
- Further improve error system
- Rename methods to their shorthands (e.g., `alloc_zeroed` -> zalloc)
- Remove bloated, niche `patterned` methods
- Reduce code duplication
- Improve MiMalloc error handling
- Update README.md

## Version 0.17.0 (2025-8-10)

### Commit 2 (2025-8-10)

- Add `FallibleDealloc` trait under `fallible_dealloc` feature
- Add `usize_bit` helper to `type_props`
- Make `unstable_util`'s `pad_layout_to_align` better match `Layout::pad_to_align`
- Improve error formatting
  - Add `err_fmt_vw` bin to view error formatting
- Safety docs
- Rename external allocation features
  - bindings to the originals are now prefixed with `mim`/`jem`
  - actual features remain prefixed with `mimalloc`/`jemalloc`
- Remove useless featuresets
- Formatting

### Commit 1 (2025-8-09)

- Improve main error system
  - Some functions that were `const` but couldn't really be used as such due to returning types that weren't `Destruct`
    (`AllocError`) now return `Destruct` subtypes of those to allow for `const` use
- `MiMalloc` now supports `os_err_reporting` with the `mimalloc_err_reporting` feature
  - `mimalloc::init_error_handler` must be called first
  - if `mimalloc_err_output` is enabled, errors will automatically be printed to stderr
- Add dedicated `FileLog` to `stats` when `stats_file_lock` is enabled
- Rename features for clarity
- Small bug fixes and doc improvements
- Sort this file's bullets to group by relation

## Version 0.16.0 (2025-8-08)

- Add `marker::SizeMeta`
- Add `Subtype` to `VarSized`
  - also switch to using `SizeMeta` instead of `Pointee<Metadata = usize>`
- Improve `AllocSlice` dropping and deallocate API
- Add growth and realloc methods to `AllocSlice` which copy and clone from existing slices
- Add os error reporting to `AllocError` with `os_error_reporting` feature (may or may not work)
  - only works for jemalloc currently
- Add file locking in `stats` with `stats_file_lock` feature (unfinished)
- Reduce code repetition and general improvements
- Switch to `tri!` macro instead of `?` operator for slight performance improvement

## Version 0.15.2 (2025-8-07)

- Fix `checked_op_panic_const` issue with MSRV
- Fix docs and some of the README

## Version 0.15.0 (2025-8-07)

### Commit 9 (2025-8-07)

- Inline alloc_slice.rs
- Improve lib.rs inlining
- Slightly improve inlining in lib.rs and helpers.rs
- Switch to manual overflow checks where necessary (using `helpers::checked_op[_panic[_const]]`)
- Use a build.rs to verify no UB before compiling
- Add some benchmarks
- Separate `std` and `libc_std` to allow using `std` on lower versions of rust (and thus libc)
- Add `AllocExt::alloc_guard_for`
- Comment out outdated portions of the readme
- Fix formatting

### Commit 8 (2025-8-07)

- Slightly improve inlining in lib.rs and helpers.rs
- Inline stats.rs

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
    honestly, it only existed because of scope creep
- Fix and improve `AllocSlice`/`AllocExt` methods
- Add `extend_slice_from_ref`, `extend_slice` and `extend_raw_slice` to `AllocSlice`
- Try to deduplicate code
- Switch to `<*mut T>::cast` instead of `as` where reasonable
- Rename `AllocError::LayoutError` to `InvalidLayout`
- Make `libc` only use `std` if `std` feature is enabled
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

- Switch to fork of jemalloc and mimalloc which fixes some issues
  - now Jemalloc has a lower MSRV
  - now jemalloc can be in the Cargo.toml without breaking everything on rust versions older than 1.61
- Finish lowering MSRV to 1.56 using `const_if!` macro
- Switch to `libc` for c types to reduce dependencies
- Add features which bind to jemalloc and mimalloc's features
- Pray I didn't break anything

### Commit 1 (2025-8-03)

- Rename `extra_const` to `extra_extra_const`
- Start lowering MSRV to 1.56 using `const_if!` macro
- Do stuff which was undone in the next commit with jemalloc and mimalloc

### Version 0.14.1 (2025-8-01)

- Fix MSRV as best as I can (1.63.0 → 1.61.0)
- Remove `v1_61` feature
- Add `extra_const` feature which makes some more methods `const` at the cost of raising the MSRV (1.61.0 -→ 1.83.0)
- Add remaining docs to AllocSlice
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

- Lowered MSRV from 1.56 to 1.40
- Started changelog
