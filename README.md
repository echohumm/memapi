# memapi

![crates.io](https://img.shields.io/crates/v/memapi.svg) ![docs.rs](https://docs.rs/memapi/badge.svg)

A minimal, `no_std`-friendly memory allocation interface for managing raw buffers, suitable for use in collections.

note: this readme is very outdated

---

## Features

* **Error reporting via `AllocError`**
* **`no_std` compatible**
* Optional **nightly/allocator_api** support via `allocator_api` feature
* **Extension methods** via `alloc_ext` feature
* Optional **unstable utilities** via `unstable_util` feature
* Optional **allocation statistics** via `stats` feature
* Zero-cost wrapper over the global allocator
* Fall-back implementation for stable Rust
* Allocation, deallocation, grow/shrink, and realloc operations

---

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
memapi = "0.12.1"
```

Or, the recommended way:

```toml
[features]
allocator_api = ["memapi/nightly"]

[dependencies]
memapi = "0.12.1"
```

---

## API

### Trait: `Alloc`

Defines the minimal allocation interface. Methods include:

* `alloc(layout) -> Result<NonNull<u8>, AllocError>`
    * `alloc_zeroed(layout) -> Result<NonNull<u8>, AllocError>`
    * `alloc_filled(layout, u8) -> Result<NonNull<u8>, AllocError>`
    * `alloc_patterned(layout, F) -> Result<NonNull<u8>, AllocError>`
* `alloc_count<T>(count) -> Result<NonNull<T>, AllocError>`
    * `alloc_count_zeroed<T>(count)`
    * `alloc_count_filled<T>(count, u8)`
    * `alloc_count_patterned<T, F>(count, pattern)`
* `dealloc(ptr, layout)`
    * `drop_and_dealloc<T: ?Sized>(ptr)`
* `grow`
    * `grow_zeroed`
    * `grow_filled`
    * `grow_patterned`
* `shrink`
* `realloc`
    * `realloc_zeroed`
    * `realloc_filled`
    * `realloc_patterned`

### Trait: `AllocExt` (feature = `alloc_ext`)

Extension methods built on top of `Alloc` for common allocation patterns:

* `alloc_write<T>(data: T) -> Result<NonNull<T>, AllocError>`
* `alloc_clone_to<T: Clone>(&T) -> Result<NonNull<T>, AllocError>`
* `alloc_clone_slice_to<T: Clone>(&[T]) -> Result<NonNull<[T]>, AllocError>`
* `alloc_slice_with<T, F: Fn(usize) -> T>(usize, F) -> Result<NonNull<[T]>, AllocError>`
* Deallocation helpers for slices and values
* Safe and unsafe variants for copying unsized data

### Traits and Utilities

* `Thin` – Marker trait for pointers with no metadata
* `UnsizedCopy` – Marker trait for safely copying raw memory
* `SizedProps` – Compile-time constants (`SZ`, `ALIGN`, `LAYOUT`, `IS_ZST`, `MAX_SLICE_LEN`) for sized types
* `PtrProps<T: ?Sized>` – Query size, alignment, layout, ZST-status, max slice length, and metadata of pointers

---

## No-Std Support

This crate works without the Rust standard library. It relies on `alloc` from the core
distribution.

---

## Documentation

* [API Reference on docs.rs](https://docs.rs/memapi)
* In-code documentation with a feature set via `cargo doc --open` with feature flags

---

## License

Licensed under **Apache-2.0** OR **MIT**. See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT).
