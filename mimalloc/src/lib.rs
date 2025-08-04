#![no_std]

use core::ffi::c_void;

extern crate libc;

#[cfg(feature = "extended")]
mod extended;
#[cfg(feature = "extended")]
pub use extended::*;

extern "C" {
    /// Allocate zero-initialized `size` bytes.
    ///
    /// Returns a pointer to newly allocated zero-initialized memory, or null if out of memory.
    pub fn mi_zalloc(size: usize) -> *mut c_void;

    /// Allocate `size` uninitialized bytes.
    ///
    /// Returns a pointer to the allocated memory or null if out of memory. The pointer will still
    /// be unique if `size` is 0.
    pub fn mi_malloc(size: usize) -> *mut c_void;

    /// Reallocates memory to `new_size` bytes.
    ///
    /// Returns a pointer to the allocated memory or null if out of memory.
    ///
    /// If null is returned, the pointer `p` is not freed. Otherwise, the original pointer is either
    /// freed or returned as the result if the reallocation fits in-place with the new size.
    ///
    /// If `p` is null, this is equivalent to [`mi_malloc`]. If `new_size` is larger than the
    /// original `size` allocated for `p`, the bytes after `size` are uninitialized.
    pub fn mi_realloc(p: *mut c_void, new_size: usize) -> *mut c_void;

    /// Allocate `size` zeroed bytes with an alignment of `align`, initialized to zero.
    ///
    /// Returns a pointer to the allocated memory or null if out of memory. The pointer will still
    /// be unique if `size` is 0.`
    pub fn mi_zalloc_aligned(size: usize, align: usize) -> *mut c_void;

    /// Allocate `size` uninitialized bytes with an alignment of `align`.
    ///
    /// Returns a pointer to the allocated memory or null if out of memory. The pointer will still
    /// be unique if `size` is 0.`
    pub fn mi_malloc_aligned(size: usize, align: usize) -> *mut c_void;

    /// Re-allocate memory to a size of `new_size` bytes, with an alignment of `align`.
    ///
    /// Returns a pointer to the allocated memory or null if out of memory.
    ///
    /// If null is returned, the pointer `p` is not freed. Otherwise, the original pointer is either
    /// freed or returned as the result if the reallocation fits in-place with the new size.
    ///
    /// If `p` is null, this is equivalent to [`mi_malloc_aligned`]. If `new_size` is
    /// larger than the original `size` allocated for `p`, the bytes after `size` are uninitialized.
    pub fn mi_realloc_aligned(p: *mut c_void, new_size: usize, align: usize) -> *mut c_void;

    /// Deallocates previously allocated memory.
    ///
    /// The pointer `p` must have been allocated before or be null.
    pub fn mi_free(p: *mut c_void);
}
