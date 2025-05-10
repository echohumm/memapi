# memapi

![crates.io](https://img.shields.io/crates/v/memapi.svg) ![docs.rs](https://docs.rs/memapi/badge.svg)

A minimal, `no_std`-friendly memory allocation interface for managing raw buffers, suitable for use in collections.

---

## Features

* **Error reporting via `AllocError`**
* **`no_std` compatible**
* Optional \[nightly] support via `allocator_api` feature
* Zero-cost wrapper over the global allocator
* Fall-back implementation for stable Rust
* Allocation, deallocation, grow/shrink, and realloc operations

---

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
memapi = "0.3.5"
```

If you want to enable the nightly allocator API integration, enable the `nightly` feature:

```toml
[dependencies.memapi]
version = "0.3.5"
features = ["nightly"]
```

---

## API

### Trait: `Alloc`

Defines the minimal allocation interface. Methods include:

* `alloc(layout) -> Result<NonNull<u8>, AllocError>`
* `alloc_zeroed(layout) -> Result<NonNull<u8>, AllocError>`
* `alloc_filled(layout, u8) -> Result<NonNull<u8>, AllocError>`
* `alloc_patterned(layout, F) -> Result<NonNull<u8>, AllocError>`
* `dealloc(ptr, layout)`
* `grow` / `grow_zeroed` / `grow_filled` / `grow_patterned`
* `shrink`
* `realloc` / `realloc_zeroed` / `realloc_filled` / `realloc_patterned`

Also provides convenience helpers for counts and zeroed/patterned/fill variants.

### Struct: `DefaultAlloc`

A zero-cost wrapper delegating to the global allocator:

* On **stable** Rust, uses `alloc::alloc::{alloc, alloc_zeroed, dealloc}`.
* On **nightly** with `allocator_api`, implements `core::alloc::Allocator` and forwards to `Global`.

### Enum: `AllocError`

Possible error cases:

| Variant                           | Meaning                                              |
|-----------------------------------|------------------------------------------------------|
| `LayoutError(size, align)`        | Invalid layout computed for given size and alignment |
| `AllocFailed(layout)`             | Underlying allocator failed                          |
| `GrowSmallerNewLayout(old, new)`  | Attempted to grow to a smaller size                  |
| `ShrinkBiggerNewLayout(old, new)` | Attempted to shrink to a larger size                 |

Implements `Debug`, `Display`, and `std::error::Error`.

---

## No-Std Support

This crate is written to work without the Rust standard library. Simply depend on `memapi` in your `#![no_std]` project;
it will pull in `alloc` from the core Rust distribution.

---

## Documentation

* [API Reference on docs.rs](https://docs.rs/memapi)
* In-code documentation is available via `cargo doc --open`.

---

## License

Licensed under **Apache-2.0** OR **MIT**. See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) for
details.
