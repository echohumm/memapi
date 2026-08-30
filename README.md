[//]: # (TODO: expand this)
# memapi2

![crates.io](https://img.shields.io/crates/v/memapi2.svg)
![docs.rs](https://docs.rs/memapi2/badge.svg)

A small, `no_std`/`no_alloc`-friendly allocation interface for raw buffers, with explicit layouts, split allocator
traits, and structured errors.

Version: 0.12.1

MSRV: 1.46.0 (some features require newer compilers or nightly; see [Feature flags](#feature-flags))

## Highlights

- Split allocator traits: `Alloc`, `Dealloc`, `Realloc`, plus `BasicAlloc` and
  `FullAlloc` aliases
- Mutable versions of allocator traits for allocation operations which require mutable access to the allocator
- Stateless allocator trait family (`traits::zst_alloc`: `ZstAlloc`, `ZstDealloc`, `ZstRealloc`,
  `ZstBasicAlloc`, `ZstFullAlloc`) exposing associated functions instead of `&self` methods, for
  allocators with no per-instance state
- Checked allocation traits (`alloc_checked_trait` feature) which return an error on invalid
  arguments instead of causing undefined behavior
- Temporary/scoped allocation trait for function-scoped allocations (AllocTemp), plus a stateless counterpart
  (`ZstAllocTemp`)
- `AllocDescriptor` trait describing an allocator's supported `AllocFeatures` and minimum alignment
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
memapi2 = "0.12.1"
```

If you want common optional features:

```toml
[dependencies]
memapi2 = { version = "0.12.1", features = ["full_std"] }
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
- `alloc_checked_trait`: checked allocation traits (`traits::alloc_checked`) which return an error on
  invalid arguments instead of causing undefined behavior
- `catch_unwind`: catch unwinds across the C boundary in `stack_alloc` (requires `std`)
- `wip_stdlib_data`: VERY wip, do not attempt to use
- `c_alloc`: C `posix_memalign`-style allocator (`c_alloc::CAlloc`)
- `stack_alloc`: `alloca`-based allocator (`stack_alloc::StackAlloc`, requires a C toolchain, MSRV on macOS is ~1.56)
- `metadata`: nightly `core::ptr::Pointee` and `core::ptr::metadata` metadata support
- `no_alloc`: disable the `alloc` crate (removes `DefaultAlloc`, `StdLayout`, and implementations for the `System`
  allocator, unless `std` is on)
- `no_nightly`: disable automatic nightly detection in `build.rs`
- `full`: convenience bundle (`c_alloc`, `alloc_checked_trait`, `stack_alloc`)
- `full_nightly`: `full` + `metadata`
- `full_std`: `full` + `catch_unwind` + `os_err_reporting`
- `full_nightly_std`: `full_nightly` + `full_std`

## Documentation

- API reference: https://docs.rs/memapi2

## License

Licensed under **GPL-3.0** OR **MIT**. See `LICENSE-GPL` and `LICENSE-MIT`.
