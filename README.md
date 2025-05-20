# memapi

![crates.io](https://img.shields.io/crates/v/memapi.svg) ![docs.rs](https://docs.rs/memapi/badge.svg)

A minimal, `no_std`-friendly memory allocation interface for managing raw buffers, suitable for use in collections.

---

## Features

* **Error reporting via `AllocError`**
* **`no_std` compatible**
* Optional **nightly** support via `allocator_api` feature
* Zero-cost wrapper over the global allocator
* Fall-back implementation for stable Rust
* Allocation, deallocation, grow/shrink, and realloc operations
* **Extension methods via `alloc_ext` feature**

---

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
memapi = "0.4.7"
```

To enable the nightly allocator API integration:

```toml
[dependencies.memapi]
version = "0.4.7"
features = ["nightly"]
```

To enable the alloc extension methods:

```toml
[dependencies.memapi]
version = "0.4.7"
features = ["alloc_ext"]
```

---

## API

### Trait: `Alloc`

Defines the minimal allocation interface. Methods include:

* `alloc(layout) -> Result<NonNull<u8>, AllocError>`
  Attempts to allocate a block fitting the given `Layout`.
  **Errors:** `AllocError::AllocFailed(layout)` if allocation fails.
* `alloc_zeroed(layout) -> Result<NonNull<u8>, AllocError>`
  Allocates zero-initialized memory.
  **Errors:** `AllocError::AllocFailed(layout)` if allocation fails.
* `alloc_filled(layout, u8) -> Result<NonNull<u8>, AllocError>`
  Allocates memory filled with the specified byte.
  **Errors:** `AllocError::AllocFailed(layout)` if allocation fails.
* `alloc_patterned(layout, F) -> Result<NonNull<u8>, AllocError>`
  Allocates memory and fills each byte via `pattern(i)`.
  **Errors:** `AllocError::AllocFailed(layout)` if allocation fails.
* Convenience helpers:

    * `alloc_count<T>(count) -> Result<NonNull<T>, AllocError>`
      **Errors:** `AllocError::LayoutError` if size too large, or `AllocError::AllocFailed(layout)`.
    * `alloc_count_zeroed<T>(count)`
    * `alloc_count_filled<T>(count, u8)`
    * `alloc_count_patterned<T, F>(count, pattern)`
* `dealloc(ptr, layout)`
  **Safety:** Must match a prior `alloc` call.
* `drop_and_dealloc<T: ?Sized>(ptr)`
  Drops the value then deallocates.
  **Safety:** `ptr` must be valid for reads and writes, aligned, and allocated by this allocator.
* `grow` / `grow_zeroed` / `grow_filled` / `grow_patterned`
  Expands a block, optionally initializing new bytes.
  **Errors:** `AllocError::GrowSmallerNewLayout` if new < old, or `AllocError::AllocFailed(layout)`.
* `shrink`
  Contracts a block.
  **Errors:** `AllocError::ShrinkBiggerNewLayout` if new > old, or `AllocError::AllocFailed(layout)`.
* `realloc` / `realloc_zeroed` / `realloc_filled` / `realloc_patterned`
  Reallocate, growing or shrinking in one step.
  **Errors:** See grow/shrink variants.

All methods are `#[track_caller]` for better diagnostics.

### Trait: `AllocExt` (feature = `alloc_ext`)

Extension methods built on top of `Alloc` for common allocation patterns:

* `alloc_write<T>(data: T) -> Result<NonNull<T>, AllocError>`
  Allocates and writes a single `T`.
  **Errors:** `AllocError::AllocFailed` on allocation failure.
* `alloc_clone_to<T: Clone>(&T) -> Result<NonNull<T>, AllocError>`
  Allocates and clones a `T` into newly allocated space.
  **Errors:** `AllocError::AllocFailed` on allocation failure.
* `alloc_clone_slice_to<T: Clone>(&[T]) -> Result<NonNull<[T]>, AllocError>`
  Allocates and clones each element of a slice.
  **Errors:** `AllocError::AllocFailed` on allocation failure.
* `dealloc_slice<T>(NonNull<[T]>)`
  Deallocates a previously allocated slice.
  **Safety:** Must match one of the clone/write methods.
* `drop_and_dealloc_slice<T>(NonNull<[T]>)`
  Drops slice contents then deallocates.
  **Safety:** Must match one of the clone/write methods.
* `alloc_copy_ref_to<T: ?Sized + UnsizedCopy>(&T) -> Result<NonNull<T>, AllocError>`
  Safe wrapper to allocate and copy unsized data by reference.
  **Errors:** `AllocError::AllocFailed`.
* `alloc_copy_ptr_to<T: ?Sized + UnsizedCopy>(*const T) -> Result<NonNull<T>, AllocError>`
  Safe wrapper to allocate and copy unsized data by pointer.
  **Errors:** `AllocError::AllocFailed`.
* `alloc_copy_ref_to_unchecked<T: ?Sized>(&T) -> Result<NonNull<T>, AllocError>`
  Unsafe version without layout checks.
  **Safety:** Caller ensures validity and metadata.
* `alloc_copy_ptr_to_unchecked<T: ?Sized + UnsizedCopy>(*const T) -> Result<NonNull<T>, AllocError>`
  Unsafe version copying unsized data by pointer.
  **Safety:** Caller ensures validity.

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
