# memapi2

![crates.io](https://img.shields.io/crates/v/memapi2.svg) ![docs.rs](https://docs.rs/memapi2/badge.svg)

A small, `no_std`/`no_alloc`-friendly allocation interface for raw buffers, with explicit layouts,
split allocator traits, and structured errors.

MSRV: 1.46.0 (some features require newer compilers or nightly; see Feature flags)

## Highlights

- Split allocator traits: `Alloc`, `Dealloc`, `Grow`, `Shrink`, `Realloc`, plus `BasicAlloc` and
  `FullAlloc` aliases
- Custom `Layout` type with conversion to/from `alloc::alloc::Layout` (unless `no_alloc` is on)
- Structured error reporting via `Error` and `Cause`, with optional OS error capture
- Optional allocator implementations: `DefaultAlloc`, `std::alloc::System`, `c_alloc::CAlloc`,
  `stack_alloc::StackAlloc` (experimental)
- Data utilities for size/alignment/metadata via `data::type_props` and `data::marker`
- `no_std` by default; `alloc` is used unless `no_alloc` is enabled

## Installation

```toml
[dependencies]
memapi2 = "0.8.1"
```

If you want common optional features:

```toml
[dependencies]
memapi2 = { version = "0.8.1", features = ["os_err_reporting", "c_alloc"] }
```

## Example

```rust
use memapi2::{DefaultAlloc, Layout, traits::*};

fn main() -> Result<(), memapi2::error::Error> {
    let alloc = DefaultAlloc;
    let layout = Layout::from_size_align(64, 8)?;

    let ptr = alloc.alloc(layout)?;
    unsafe {
        core::ptr::write_bytes(ptr.as_ptr(), 0xCD, layout.size());
        alloc.try_dealloc(ptr, layout)?;
    }

    Ok(())
}
```

## Feature flags

- `std`: enable `std` integration (including `std::alloc::System`)
- `os_err_reporting`: best-effort OS error reporting via `errno` (requires `std`)
- `alloc_mut_traits`: mutable allocator trait variants (`AllocMut`, `DeallocMut`, ...)
- `alloc_temp_trait`: scoped/temporary allocation trait (`AllocTemp`)
- `c_alloc`: C `aligned_alloc`-style allocator (`c_alloc::CAlloc`)
- `stack_alloc`: `alloca`-based allocator (`stack_alloc::StackAlloc`, experimental, requires a C
  toolchain)
- `c_str`: enable `CStr`-specific data traits in `no_std` (MSRV: 1.64)
- `metadata`: nightly `core::ptr::Pointee` metadata support
- `sized_hierarchy`: nightly `core::marker::MetaSized` support
- `no_alloc`: disable the `alloc` crate (removes `DefaultAlloc`, `StdLayout`, and implementations
  for the `System` allocator)
- `no_nightly`: disable automatic nightly detection in `build.rs`
- `full_msrv`: convenience bundle (`os_err_reporting`, `c_alloc`, `stack_alloc`, `alloc_mut_traits`)
- `full`: `full_msrv` + `c_str`
- `all_nightly`: `metadata` + `sized_hierarchy`
- `full_nightly`: `full` + `all_nightly`

## Notes

- `DefaultAlloc` delegates to the global allocator. Do not set it as the global allocator itself,
  or you will cause infinite recursion.
- This crate is low-level and uses raw pointers. Read the safety contracts on trait methods and
  layout constructors carefully.

## Documentation

- API reference: https://docs.rs/memapi2

## License

Licensed under **GPL-3.0** OR **MIT**. See `LICENSE-GPL` and `LICENSE-MIT`.
