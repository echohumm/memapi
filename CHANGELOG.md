# memapi changelog

_no versions before 0.13.2 have a changelog as I started the changelog in that version and have not yet backtracked._

## Table of Contents

- [0.15.0 Predicted](#0150-predicted)
- [Version 0.14.1](#version-0141)
  - [Commit 3 Predicted](#commit-3-predicted)
  - [Commit 2 Predicted](#commit-2-predicted)
  - [Commit 1 (2025-8-01)](#commit-1-2025-8-01)
- [Version 0.14.0](#version-0140-not-published-to-cratesio-skipping-to-0141-for-users)
  - [Commit 3 (2025-7-27)](#commit-3-2025-7-27)
  - [Commit 2 (2025-7-26)](#commit-2-2025-7-26)
  - [Commit 1 (2025-7-26)](#commit-1-2025-7-26)
- [Version 0.13.2](#version-0132-2025-7-25)

## 0.15.0 [Predicted]

- Proper tests for many untested methods
- Proper benchmarks
- Finish filling API holes in `AllocSlice`
  - with docs this time
- Performance and binary size improvements
  - make as many sections as possible `const` [perf]
  - reduce inlining [size]
  - use helpers for repetitive code [size]
- Lower const MSRV (if possible)
- Split AllocSlice/AllocExt into multiple traits (only in consideration)

## Version 0.14.1

## Commit 2 [Predicted]

- Debloat the primary surfaces
- Implement some small TODOs (just search for them pls i'm too tired to list them here)
- Rename `extra_const` to `extra_extra_const`
- Further lower the MSRV (many methods' constness are now behind the new `extra_const`)
- Finally make `owned` stuff use the right MSRV and the `extra_const`/`extra_extra_const` features

## Commit 1 (2025-8-01)

- Fix MSRV as best as I can (1.63.0 → 1.61.0), some stuff may unnecessarily support older versions
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
      actual msrv and it fails

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
