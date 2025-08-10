# memapi

![crates.io](https://img.shields.io/crates/v/memapi.svg) ![docs.rs](https://docs.rs/memapi/badge.svg)

A `no_std`-friendly memory allocation interface for managing raw buffers, suitable for use in collections.

MSRV: 1.56

MSRV with `extra_const` feature: 1.61

Mimalloc/Jemalloc MSRV: 1.63

MSRV with `c_str`/`stats_parking_lot` feature: 1.64

MSRV with `extra_extra_const` feature: 1.83

MSRV with `stats_file_lock` feature: 1.89

---

## Features

## Features

- Allocation primitives: allocation, deallocation, grow/shrink, and realloc operations
- Allocation statistics (feature: `stats`)
- Allocator API support on nightly (feature: `nightly`)
  - Clone/Copy specialization for performance and ease of use (feature: `specialization`)
  - CloneToUninit usage in some functions (feature: `clone_to_uninit`)
  - Pointer metadata usage in some functions (feature: `metadata`)
  - Sized hierarchy support (feature: `sized_hierarchy`)
- C-style string support (feature: `c_str`) (MSRV: 1.64)
- Constants: extra (feature: `extra_const`) (MSRV: 1.61)
- Constants: even more (feature: `extra_extra_const`) (MSRV: 1.83)
- Error reporting via `AllocError`
- External allocator support (MSRV: 1.63)
  - jemalloc (feature: `jemalloc`)
  - mimalloc (feature: `mimalloc`)
- Fallback implementation for stable Rust
- Low-cost wrapper over the global allocator
- `no_std` compatible
- Resize-in-place extension methods (feature: `resize_in_place`)
- Basic extension methods (feature: `alloc_ext`)
- Slice-focused extension methods (feature: `alloc_slice`)
- `std` support (feature: `std`)
- Unstable utilities (feature: `unstable_util`)

---

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
memapi = "0.15.0"
```

Or, the recommended way:

```toml
[features]
allocator_api = ["memapi/nightly"]

[dependencies]
memapi = "0.15.0"
```

---

## Benchmarks

| Benchmark                     | Base (ns) | Crate (ns) | Ratio  | Δ vs base    |
|------------------------------|----------:|-----------:|:------:|-------------:|
| alloc                        |    4.2217 |     4.3979 | 1.0417× |   4.17% slower |
| alloc_default<u64>           |    3.9590 |     4.4648 | 1.1277× |  12.77% slower |
| alloc_write<u128>            |    7.5617 |     4.2021 | 0.5557× |  44.43% faster |
| alloc_filled_1k              |   23.2630 |    28.5900 | 1.2288× |  22.88% slower |
| alloc_patterned_2k           |  840.0900 |   836.9500 | 0.9963× |   0.37% faster |
| grow_filled_1k_to_4k         |  104.9400 |    93.9140 | 0.8950× |  10.50% faster |
| realloc_filled_4k_to_1k      |   81.0100 |    72.2300 | 0.8918× |  10.82% faster |
| dealloc_typed<usize>         |    4.1694 |     4.5512 | 1.0916× |   9.16% slower |
| zero_and_dealloc_8k          |  102.8900 |   151.5100 | 1.4727× |  47.27% slower |

### Notes

- Numbers are medians reported by Criterion as can be seen in [bench.rs](./benches/bench.rs).
- Ratios < 1.0 mean the crate is faster than the base; > 1.0 means slower.
- Any faster results are most likely error. I tried to use `black_box` everywhere to minimize optimizer tomfoolery, but
  this is inevitable.

---

[//]: # (## API)

[//]: # (### Trait: `Alloc`)

[//]: # ()

[//]: # (Defines the minimal allocation interface. Methods include:)

[//]: # ()

[//]: # (* `alloc&#40;layout&#41; -> Result<NonNull<u8>, AllocError>`)

[//]: # (    * `alloc_zeroed&#40;layout&#41; -> Result<NonNull<u8>, AllocError>`)

[//]: # (    * `alloc_filled&#40;layout, u8&#41; -> Result<NonNull<u8>, AllocError>`)

[//]: # (    * `alloc_patterned&#40;layout, F&#41; -> Result<NonNull<u8>, AllocError>`)

[//]: # (* `alloc_count<T>&#40;count&#41; -> Result<NonNull<T>, AllocError>`)

[//]: # (    * `alloc_count_zeroed<T>&#40;count&#41;`)

[//]: # (    * `alloc_count_filled<T>&#40;count, u8&#41;`)

[//]: # (    * `alloc_count_patterned<T, F>&#40;count, pattern&#41;`)

[//]: # (* `dealloc&#40;ptr, layout&#41;`)

[//]: # (    * `drop_and_dealloc<T: ?Sized>&#40;ptr&#41;`)

[//]: # (* `grow`)

[//]: # (    * `grow_zeroed`)

[//]: # (    * `grow_filled`)

[//]: # (    * `grow_patterned`)

[//]: # (* `shrink`)

[//]: # (* `realloc`)

[//]: # (    * `realloc_zeroed`)

[//]: # (    * `realloc_filled`)

[//]: # (    * `realloc_patterned`)

[//]: # ()

[//]: # (### Trait: `AllocExt` &#40;feature = `alloc_ext`&#41;)

[//]: # ()

[//]: # (Extension methods built on top of `Alloc` for common allocation patterns:)

[//]: # ()

[//]: # (* `alloc_write<T>&#40;data: T&#41; -> Result<NonNull<T>, AllocError>`)

[//]: # (* `alloc_clone_to<T: Clone>&#40;&T&#41; -> Result<NonNull<T>, AllocError>`)

[//]: # (* `alloc_clone_slice_to<T: Clone>&#40;&[T]&#41; -> Result<NonNull<[T]>, AllocError>`)

[//]: # (* `alloc_slice_with<T, F: Fn&#40;usize&#41; -> T>&#40;usize, F&#41; -> Result<NonNull<[T]>, AllocError>`)

[//]: # (* Deallocation helpers for slices and values)

[//]: # (* Safe and unsafe variants for copying unsized data)

[//]: # ()

[//]: # (### Traits and Utilities)

[//]: # ()

[//]: # (* `Thin` – Marker trait for pointers with no metadata)

[//]: # (* `UnsizedCopy` – Marker trait for safely copying raw memory)

[//]: # (* `SizedProps` – Compile-time constants &#40;`SZ`, `ALIGN`, `LAYOUT`, `IS_ZST`, `MAX_SLICE_LEN`&#41; for sized types)

[//]: # (* `PtrProps<T: ?Sized>` – Query size, alignment, layout, ZST-status, max slice length, and metadata of pointers)

[//]: # ()

[//]: # (---)

[//]: # ()

## No-Std Support

This crate works without the Rust standard library. It relies on `alloc` from the core distribution.

---

## Documentation

- [API Reference on docs.rs](https://docs.rs/memapi)
- In-code documentation with a feature set via `cargo doc --open` with feature flags

---

## License

Licensed under **Apache-2.0** OR **MIT**. See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT).
