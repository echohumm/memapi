# memapi changelog

_no versions before 0.13.2 have a changelog as I started the changelog in that version and have not yet backtracked._

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
- Split AllocExt into multiple traits (only in consideration)

## Version 0.14.0 

### Commit 1 (2025-7-26)

- Lowered MSRV from 1.40 to 1.36
- Switched to `cty` crate for all C types
- Fixed `AllocExt::alloc_clone_to` variant used when the `clone_to_uninit` feature is enabled but `metadata` isn't
- Started filling API holes in `AllocSlice` (grow/realloc with a predicate, initialization function, or defaulting)
  - docs are missing
- Added `set_init` to `helpers::AllocSliceGuard` to set the initialized element count for use with partially initialized
  data
- Added `USIZE_MAX_NO_HIGH_BIT` to `type_props` to avoid repetition

### Commit 2 [Predicted]

- Add missing docs for `AllocSlice` methods
- Small fixes (if any issues are found)

## Version 0.13.2 (2025-7-25)

- Started changelog
- Lowered MSRV from 1.56 to 1.40
