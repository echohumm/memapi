# memapi2

![crates.io](https://img.shields.io/crates/v/memapi2.svg)
![docs.rs](https://docs.rs/memapi2/badge.svg)

A small, `no_std`/`no_alloc`-friendly allocation interface for raw buffers, with explicit layouts,
split allocator traits, and structured errors.

Version: 0.11.4

MSRV: 1.46.0 (some features require newer compilers or nightly; see [Feature flags](#feature-flags))

## Highlights

- Split allocator traits: `Alloc`, `Dealloc`, `Grow`, `Shrink`, `Realloc`, plus `BasicAlloc` and
  `FullAlloc` aliases
- Mutable versions of allocator traits for allocation operations which require mutable access to the
  allocator
- Temporary/scoped allocation trait for function-scoped allocations
- Custom `Layout` type with conversion to/from `alloc::alloc::Layout` (unless `no_alloc` is on and
  `std` isn't)
- Generic `Error` types for allocation traits
- Structured error reporting via `Error` and `Cause`, with optional OS error capture
- Optional allocator implementations: `DefaultAlloc`, `std::alloc::System`, `c_alloc::CAlloc`,
  `stack_alloc::StackAlloc`
- Data utilities for size/alignment/metadata via `traits::data::type_props` and
  `traits::data::marker`
- `no_std` by default; `alloc` is used unless `no_alloc` is enabled (`std` is used in place of
  `alloc` if `std` and `no_alloc` are both enabled)

## Installation

```toml
[dependencies]
memapi2 = "0.11.4"
```

If you want common optional features:

```toml
[dependencies]
memapi2 = { version = "0.11.4", features = ["os_err_reporting"] }
```

## Example

```rust
use memapi2::{DefaultAlloc, Layout, traits::*};

fn main() -> Result<(), memapi2::error::Error> {
    let alloc = DefaultAlloc;
    let layout = Layout::from_size_align(64, 8)?;

    let ptr = alloc.alloc(layout)?;
    unsafe {
        ::core::ptr::write_bytes(ptr.as_ptr(), 0xCD, layout.size());
        alloc.try_dealloc(ptr, layout)?;
    }

    Ok(())
}
```

## Feature flags

- `std`: enable `std` integration (including `std::alloc::System`)
- `os_err_reporting`: best-effort OS error reporting via `errno` (requires `std`)
- `alloc_temp_trait`: scoped/temporary allocation trait (`AllocTemp`)
- `c_alloc`: C `posix_memalign`-style allocator (`c_alloc::CAlloc`)
- `stack_alloc`: `alloca`-based allocator (`stack_alloc::StackAlloc`, requires a C toolchain)
- `metadata`: nightly `core::ptr::Pointee` and `core::ptr::metadata` metadata support
- `no_alloc`: disable the `alloc` crate (removes `DefaultAlloc`, `StdLayout`, and implementations
  for the `System` allocator, unless `std` is on)
- `no_nightly`: disable automatic nightly detection in `build.rs`
- `full`: convenience bundle (`os_err_reporting`, `c_alloc`, `stack_alloc`)
- `full_nightly`: `full` + `metadata`

## Notes

- `DefaultAlloc` delegates to the global allocator. Do not set it as the global allocator itself,
  or you will cause infinite recursion.
- This crate is low-level and uses raw pointers. Read the safety contracts on trait methods and
  layout constructors carefully.

## Documentation

- API reference: https://docs.rs/memapi2

## License

Licensed under **GPL-3.0** OR **MIT**. See `LICENSE-GPL` and `LICENSE-MIT`.
