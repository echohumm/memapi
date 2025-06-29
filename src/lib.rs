//! `memapi` provides a minimal, `no_std`-friendly memory allocation interface
//! for managing raw buffers, suitable for use in collections.
//!
//! This crate exports:
//!
//! - [`Alloc`], a trait defining basic allocate, deallocate, grow, and shrink operations.
//! - [`DefaultAlloc`], a zero-cost wrapper delegating to the global allocator.
//! - [`AllocError`], an enum of possible error cases.
//!
//! - [`PtrProps`](PtrProps), properties getters for pointers to values.
//! - [`SizedProps`], properties for sized types. Similar to the unstable
//!   [`SizedTypeProperties`](core::mem::SizedTypeProperties).
//!
//! - [`UnsizedCopy`], a marker trait indicating a value can be copied safely even if unsized.
//! - [`Thin`], a marker trait indicating a pointer to a type has no metadata.
//!
//! And, if the `alloc_ext` feature is on:
//!
//! - `AllocExt`, defining abstractions over Alloc's API.
//!
//! # Examples
//!
//! ```rust
//! # use memapi::{Alloc, DefaultAlloc, error::AllocError};
//! # use core::{
//! #    alloc::Layout,
//! #    ptr::NonNull
//! # };
//! let allocator = DefaultAlloc;
//! // Allocate 4 usizes.
//! let ptr = allocator.alloc_slice::<usize>(4).expect("alloc failed").cast::<usize>();
//! unsafe {
//!     for i in 0..4 {
//!         ptr.add(i).write(17384 * i + 8923)
//!     }
//! }
//! // Deallocate the block.
//! unsafe { allocator.dealloc_n(ptr, 4) };
//! ```

// TODO: maybe update the readme
// TODO: change most of the track_caller attrs into cfg_attr(miri, track_caller), as they are only
//  useful then.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "metadata", feature(ptr_metadata))]
#![cfg_attr(feature = "clone_to_uninit", feature(clone_to_uninit))]
#![cfg_attr(feature = "specialization", feature(min_specialization))]
#![allow(unsafe_op_in_unsafe_fn, internal_features)]
#![deny(missing_docs)]

extern crate alloc;
extern crate core;

use crate::error::Err;
#[cfg(feature = "alloc_ext")]
pub use alloc_ext::*;
#[cfg(feature = "resize_in_place")]
pub use in_place::*;

// TODO: when my ide actually works, move stats, owned, in_place, and alloc_ext to ./features/*.rs
//  because they are only active when a feature is on.

/// Marker traits.
pub mod marker;
/// Sized type properties as constants and property getters for pointers.
pub mod type_props;

/// Small alternatives to Rust functions which are currently unstable.
pub mod unstable_util;

/// Errors which can occur during allocation.
pub mod error;

mod features;

#[allow(unused_imports)]
pub use features::*;

pub(crate) mod external_alloc;

pub use external_alloc::*;

use crate::{
    error::AllocError,
    helpers::{dangling_nonnull_for, layout_or_sz_align, null_q, AllocGuard},
};
use alloc::alloc::{
    alloc as raw_all, alloc_zeroed as raw_allz, dealloc as de, GlobalAlloc, Layout,
};
use core::{
    cmp::Ordering,
    ptr::{null_mut, NonNull},
    error::Error
};

/// Default allocator, delegating to the global allocator.
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefaultAlloc;

macro_rules! default_alloc_impl {
    ($ty:ty) => {
        impl Alloc for $ty {
            #[track_caller]
            #[inline]
            fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
                if layout.size() == 0 {
                    Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
                } else {
                    null_q(unsafe { raw_all(layout) }, layout)
                }
            }

            #[track_caller]
            #[inline]
            fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
                if layout.size() == 0 {
                    Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
                } else {
                    null_q(unsafe { raw_allz(layout) }, layout)
                }
            }

            #[track_caller]
            #[inline]
            unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
                if layout.size() != 0 {
                    de(ptr.as_ptr(), layout);
                }
            }
        }
    };
}

unsafe impl GlobalAlloc for DefaultAlloc {
    #[track_caller]
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        match Alloc::alloc(&self, layout) {
            Ok(ptr) => ptr.as_ptr(),
            Err(_) => null_mut(),
        }
    }

    #[track_caller]
    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        Alloc::dealloc(&self, NonNull::new_unchecked(ptr), layout);
    }

    #[track_caller]
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        match Alloc::alloc_zeroed(&self, layout) {
            Ok(ptr) => ptr.as_ptr(),
            Err(_) => null_mut(),
        }
    }

    #[track_caller]
    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        match Alloc::realloc(
            &self,
            NonNull::new_unchecked(ptr),
            layout,
            Layout::from_size_align_unchecked(new_size, layout.align()),
        ) {
            Ok(ptr) => ptr.as_ptr(),
            Err(_) => null_mut(),
        }
    }
}

default_alloc_impl!(DefaultAlloc);

/// A memory allocation interface.
///
/// This trait does _not_ require `Self: Allocator` and is `no_std`-compatible.
///
/// # Type parameters
///
/// - `OErr: Error = Err`: The type which [`AllocError::Other(OErr)`] wraps.
pub trait Alloc<OErr: Error = Err> {
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    #[track_caller]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError<OErr>>;

    /// Attempts to allocate a block of memory for `len` instances of `T`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_slice<T>(&self, len: usize) -> Result<NonNull<[T]>, AllocError<OErr>> {
        let layout = layout_or_sz_align::<T>(len)
            .map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        self.alloc(layout)
            .map(|ptr| NonNull::slice_from_raw_parts(ptr.cast(), len))
            .map_err(|_| AllocError::AllocFailed(layout))
    }

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError<OErr>> {
        match self.alloc(layout) {
            Ok(p) => {
                unsafe {
                    p.write_bytes(0, layout.size());
                }
                Ok(p)
            }
            Err(e) => Err(e),
        }
    }

    /// Attempts to allocate a zeroed block of memory for `len` instances of `T`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_slice_zeroed<T>(&self, len: usize) -> Result<NonNull<[T]>, AllocError<OErr>> {
        let layout = layout_or_sz_align::<T>(len)
            .map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        self.alloc_zeroed(layout)
            .map(|ptr| NonNull::slice_from_raw_parts(ptr.cast(), len))
            .map_err(|_| AllocError::AllocFailed(layout))
    }

    /// Attempts to allocate a block of memory fitting the given [`Layout`], filled with bytes
    /// initialized to `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError<OErr>> {
        match self.alloc(layout) {
            Ok(p) => {
                unsafe {
                    p.as_ptr().write_bytes(n, layout.size());
                }
                Ok(p)
            }
            Err(e) => Err(e),
        }
    }

    /// Attempts to allocate a block of memory for `len` instances of `T`, filled with bytes
    /// initialized to `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_slice_filled<T>(&self, len: usize, n: u8) -> Result<NonNull<[T]>, AllocError<OErr>> {
        let layout = layout_or_sz_align::<T>(len)
            .map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        self.alloc_filled(layout, n)
            .map(|ptr| NonNull::slice_from_raw_parts(ptr.cast(), len))
            .map_err(|_| AllocError::AllocFailed(layout))
    }

    /// Attempts to allocate a block of memory fitting the given [`Layout`] and
    /// fill it by calling `pattern(i)` for each byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError<OErr>> {
        match self.alloc(layout) {
            Ok(p) => {
                let guard = AllocGuard::new(p.cast::<u8>(), self);
                for i in 0..layout.size() {
                    unsafe {
                        guard.as_ptr().add(i).write(pattern(i));
                    }
                }
                Ok(guard.release())
            }
            Err(e) => Err(e),
        }
    }

    /// Attempts to allocate a block of memory for `len` instances of `T` and
    /// fill it by calling `pattern(i)` for each byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_slice_patterned<T, F: Fn(usize) -> u8 + Clone>(
        &self,
        len: usize,
        pattern: F,
    ) -> Result<NonNull<[T]>, AllocError<OErr>> {
        let layout = layout_or_sz_align::<T>(len)
            .map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        self.alloc_patterned(layout, pattern)
            .map(|ptr| NonNull::slice_from_raw_parts(ptr.cast(), len))
            .map_err(|_| AllocError::AllocFailed(layout))
    }

    /// Deallocates a previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `layout` must describe exactly the same block.
    #[track_caller]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout);

    /// Deallocates a previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `n` must be the exact number of `T` held in that block.
    #[track_caller]
    #[inline]
    unsafe fn dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) {
        // Here, we assume the layout is valid as it was presumably used to allocate previously.
        self.dealloc(
            ptr.cast(),
            Layout::from_size_align_unchecked(size_of::<T>() * n, align_of::<T>()),
        );
    }

    /// Drops the data at a pointer and deallocates its previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and a valid `T`.
    #[track_caller]
    #[inline]
    unsafe fn drop_and_dealloc<T: ?Sized>(&self, ptr: NonNull<T>) {
        ptr.drop_in_place();
        //                             This is a bit of a hack, but for_value_raw is unstable, so...
        self.dealloc(ptr.cast::<u8>(), Layout::for_value(&*ptr.as_ptr()));
    }

    /// Drops the data at a pointer and deallocates its previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and contain `n` valid `T`.
    /// - `n` must be the exact number of `T` held in that block.
    #[track_caller]
    #[inline]
    unsafe fn drop_and_dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) {
        NonNull::slice_from_raw_parts(ptr, n).drop_in_place();
        self.dealloc_n(ptr, n);
    }

    /// Grow the given block to a new, larger layout.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    #[inline]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError<OErr>> {
        grow(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::None,
        )
    }

    /// Grows the given block to a new, larger layout, zeroing any newly allocated bytes.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] in `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    #[inline]
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError<OErr>> {
        grow(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::Zero,
        )
    }

    /// Grow the given block to a new, larger layout, filling any newly allocated bytes by calling
    /// `pattern(i)` for each new byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
    unsafe fn grow_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError<OErr>> {
        grow(self, ptr, old_layout, new_layout, AllocPattern::Fn(pattern))
    }

    /// Grows the given block to a new, larger layout, filling any newly allocated bytes with `n`.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] in `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    #[inline]
    fn grow_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<NonNull<u8>, AllocError<OErr>> {
        grow(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::All(n),
        )
    }

    /// Shrink the given block to a new, smaller layout.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_layout.size() > old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    #[inline]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError<OErr>> {
        shrink(self, ptr, old_layout, new_layout)
    }

    /// Reallocate a block, growing or shrinking as needed.
    ///
    /// On grow, preserves existing contents up to `old_layout.size()`, and
    /// on shrink, truncates to `new_layout.size()`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError<OErr>> {
        ralloc(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::None,
        )
    }

    /// Reallocate a block, growing or shrinking as needed, zeroing any newly
    /// allocated bytes.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
    unsafe fn realloc_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError<OErr>> {
        ralloc(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::Zero,
        )
    }

    /// Reallocate a block, growing or shrinking as needed, filling any new bytes by calling
    /// `pattern(i)` for each new byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
    unsafe fn realloc_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError<OErr>> {
        ralloc(self, ptr, old_layout, new_layout, AllocPattern::Fn(pattern))
    }

    /// Reallocate a block, growing or shrinking as needed, filling any newly
    /// allocated bytes with `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
    unsafe fn realloc_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<NonNull<u8>, AllocError<OErr>> {
        ralloc(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::All(n),
        )
    }
}

#[cfg(feature = "nightly")]
/// The primary module for when `nightly` is enabled.
pub(crate) mod nightly {
    use crate::{dangling_nonnull_for, error::AllocError, helpers::null_q, Alloc, DefaultAlloc};
    use alloc::alloc::{
        alloc as raw_all, alloc_zeroed as raw_allz, dealloc as de, Allocator, Global, Layout,
    };
    use core::{alloc::AllocError as AllocatorError, ptr::NonNull};

    unsafe impl Allocator for DefaultAlloc {
        #[track_caller]
        #[inline]
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocatorError> {
            Allocator::allocate(&Global, layout)
        }

        #[track_caller]
        #[inline]
        fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocatorError> {
            Allocator::allocate_zeroed(&Global, layout)
        }

        #[track_caller]
        #[inline]
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            Allocator::deallocate(&Global, ptr.cast(), layout);
        }

        #[track_caller]
        #[inline]
        unsafe fn grow(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocatorError> {
            Allocator::grow(&Global, ptr.cast(), old_layout, new_layout)
        }

        #[track_caller]
        #[inline]
        unsafe fn grow_zeroed(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocatorError> {
            Allocator::grow_zeroed(&Global, ptr.cast(), old_layout, new_layout)
        }

        #[track_caller]
        #[inline]
        unsafe fn shrink(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocatorError> {
            Allocator::shrink(&Global, ptr.cast(), old_layout, new_layout)
        }
    }

    default_alloc_impl!(Global);
}

impl<O: Error, A: Alloc<O> + ?Sized> Alloc<O> for &A {
    #[track_caller]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError<O>> {
        (**self).alloc(layout)
    }

    #[track_caller]
    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError<O>> {
        (**self).alloc_zeroed(layout)
    }

    #[track_caller]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        (**self).dealloc(ptr, layout);
    }
}

#[cfg(feature = "std")]
impl Alloc for std::alloc::System {
    #[track_caller]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        if layout.size() == 0 {
            Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
        } else {
            match NonNull::new(unsafe { GlobalAlloc::alloc(self, layout) }) {
                Some(ptr) => Ok(ptr),
                None => Err(AllocError::AllocFailed(layout)),
            }
        }
    }

    #[track_caller]
    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        if layout.size() == 0 {
            Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
        } else {
            match NonNull::new(unsafe { GlobalAlloc::alloc_zeroed(self, layout) }) {
                Some(ptr) => Ok(ptr),
                None => Err(AllocError::AllocFailed(layout)),
            }
        }
    }

    #[track_caller]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        GlobalAlloc::dealloc(self, ptr.as_ptr(), layout);
    }
}

/// Internal helper to grow the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`, filling new bytes using `pattern.`
#[inline]
#[track_caller]
fn grow<O: Error, A: Alloc<O> + ?Sized, F: Fn(usize) -> u8 + Clone>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError<O>> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => unsafe { grow_unchecked(a, ptr, old_layout, new_layout, pattern) },
        Ordering::Equal => Ok(ptr),
        Ordering::Greater => Err(AllocError::GrowSmallerNewLayout(
            old_layout.size(),
            new_layout.size(),
        )),
    }
}

/// Internal helper to shrink the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
#[inline]
#[track_caller]
fn shrink<O: Error, A: Alloc<O> + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> Result<NonNull<u8>, AllocError<O>> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => Err(AllocError::ShrinkBiggerNewLayout(
            old_layout.size(),
            new_layout.size(),
        )),
        Ordering::Equal => Ok(ptr),
        Ordering::Greater => unsafe { shrink_unchecked(a, ptr, old_layout, new_layout) },
    }
}

/// Internal helper to grow the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
///
/// # Safety
///
/// This function does not check for layout validity. `new_layout.size()` should be greater than
/// `old_layout.size()`.
#[inline]
#[track_caller]
unsafe fn grow_unchecked<O: Error, A: Alloc<O> + ?Sized, F: Fn(usize) -> u8 + Clone>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError<O>> {
    let new_ptr = match pattern {
        AllocPattern::None => a.alloc(new_layout)?.cast::<u8>(),
        AllocPattern::Fn(f) => a.alloc_patterned(new_layout, f)?,
        AllocPattern::Zero => a.alloc_zeroed(new_layout)?.cast::<u8>(),
        AllocPattern::All(n) => a.alloc_filled(new_layout, n)?.cast::<u8>(),
    };
    unsafe {
        ptr.copy_to_nonoverlapping(new_ptr, old_layout.size());
        a.dealloc(ptr, old_layout);
    }
    Ok(new_ptr)
}

/// Internal helper to shrink the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
///
/// # Safety
///
/// This function does not check for layout validity. `new_layout.size()` should be greater than
/// `old_layout.size()`.
#[inline]
#[track_caller]
unsafe fn shrink_unchecked<O: Error, A: Alloc<O> + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> Result<NonNull<u8>, AllocError<O>> {
    let new_ptr = a.alloc(new_layout)?.cast::<u8>();
    unsafe {
        ptr.copy_to_nonoverlapping(new_ptr, new_layout.size());
        a.dealloc(ptr, old_layout);
    }
    Ok(new_ptr)
}

/// Helper for realloc to reduce repetition.
#[track_caller]
#[inline]
unsafe fn ralloc<O: Error, A: Alloc<O> + ?Sized, F: Fn(usize) -> u8 + Clone>(
    alloc: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pat: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError<O>> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => unsafe { grow_unchecked(&alloc, ptr, old_layout, new_layout, pat) },
        Ordering::Equal => Ok(ptr),
        Ordering::Greater => unsafe { shrink_unchecked(&alloc, ptr, old_layout, new_layout) },
    }
}

/// The pattern to fill new bytes with.
enum AllocPattern<F: Fn(usize) -> u8 + Clone> {
    /// Don't fill bytes at all.
    None,
    /// Zero all bytes.
    Zero,
    /// Set all bytes to a specific value.
    All(u8),
    /// Get the value of the byte using the given predicate.
    Fn(F),
}

/// Helpers which tend to be useful in other libraries as well.
pub mod helpers {
    use crate::Err;
use crate::{error::AllocError, type_props::SizedProps, Alloc};
    use core::{
        alloc::Layout,
        mem::forget,
        num::NonZeroUsize,
        ops::Deref,
        ptr::NonNull,
        error::Error,
        marker::PhantomData
    };
    /// Converts a possibly null pointer into a [`NonNull`] result.
    #[inline]
    pub(crate) const fn null_q<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        if ptr.is_null() {
            Err(AllocError::AllocFailed(layout))
        } else {
            Ok(unsafe { NonNull::new_unchecked(ptr.cast()) })
        }
    }

    /// Aligns the given value up to an alignment.
    #[must_use]
    #[inline]
    pub const fn align_up(n: usize, align: usize) -> usize {
        (n + align - 1) & !(align - 1)
    }

    /// Returns a valid, dangling [`NonNull`] for the given layout.
    #[must_use]
    #[inline]
    pub const fn dangling_nonnull_for(layout: Layout) -> NonNull<u8> {
        unsafe { dangling_nonnull(layout.align()) }
    }

    /// Returns a [`NonNull`] which has the given alignment as its address.
    ///
    /// # Safety
    ///
    /// The caller must ensure the valid `alignment` would not result in a null pointer.
    #[must_use]
    #[inline]
    pub const unsafe fn dangling_nonnull(align: usize) -> NonNull<u8> {
        NonNull::without_provenance(unsafe { NonZeroUsize::new_unchecked(align) })
    }

    /// Gets either a valid layout with space for `n` count of `T`, or a raw size and alignment.
    ///
    /// # Errors
    ///
    /// Returns `Err(size, align)` if creation of a layout with the given size and alignment fails.
    #[inline]
    pub const fn layout_or_sz_align<T>(n: usize) -> Result<Layout, (usize, usize)> {
        let (sz, align) = (T::SZ, T::ALIGN);

        if sz != 0 && n > unsafe { (isize::MAX as usize + 1).unchecked_sub(align) } / sz {
            return Err((sz, align));
        }

        unsafe {
            Ok(Layout::from_size_align_unchecked(
                sz.unchecked_mul(n),
                align,
            ))
        }
    }

    /// A RAII guard that owns a single allocation and ensures it is deallocated unless explicitly
    /// released.
    ///
    /// `AllocGuard` wraps a `NonNull<T>` pointer and an allocator reference `&A`. When the guard
    /// goes out of scope, it will deallocate the underlying memory via the allocator.
    ///
    /// To take ownership of the allocation without deallocating, call
    /// [`release`](SliceAllocGuard::release), which returns the raw pointer and prevents the guard
    /// from running its cleanup.
    ///
    /// This should be used in any situation where the initialization of a pointer's data may panic.
    /// (e.g., initializing via a clone or any other user-implemented method)
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::ptr::NonNull;
    /// # use memapi::{helpers::AllocGuard, Alloc, DefaultAlloc};
    /// # let alloc = DefaultAlloc;
    /// // Allocate space for one `u32` and wrap it in a guard
    /// let layout = core::alloc::Layout::new::<u32>();
    /// let mut guard = AllocGuard::new(alloc.alloc(layout).unwrap().cast::<u32>(), &alloc);
    ///
    /// // Initialize the value
    /// unsafe { guard.as_ptr().write(123) };
    ///
    /// // If everything is OK, take ownership and prevent automatic deallocation
    /// // (commented out for this example as the pointer will not be used)
    /// // let raw = guard.release();
    /// ```
    pub struct AllocGuard<'a, T: ?Sized, A: Alloc<O> + ?Sized, O: Error = Err> {
        ptr: NonNull<T>,
        alloc: &'a A,
        _marker: PhantomData<O>,
    }

    impl<'a, O: Error, T: ?Sized, A: Alloc<O> + ?Sized> AllocGuard<'a, T, A, O> {
        /// Creates a new guard from a pointer and a reference to an allocator.
        #[inline]
        pub const fn new(ptr: NonNull<T>, alloc: &'a A) -> AllocGuard<'a, T, A, O> {
            AllocGuard { ptr, alloc, _marker: PhantomData }
        }

        /// Initializes the value by writing to the contained pointer.
        #[track_caller]
        #[inline]
        pub const fn init(&self, elem: T)
        where
            T: Sized,
        {
            unsafe {
                self.ptr.write(elem);
            }
        }

        /// Releases ownership of the allocation, preventing deallocation, and return the raw
        /// pointer.
        #[inline]
        #[must_use]
        pub const fn release(self) -> NonNull<T> {
            let ptr = self.ptr;
            forget(self);
            ptr
        }
    }

    impl<T: ?Sized, A: Alloc<O> + ?Sized, O: Error> Drop for AllocGuard<'_, T, A, O> {
        #[track_caller]
        fn drop(&mut self) {
            unsafe {
                self.alloc.dealloc(
                    self.ptr.cast::<u8>(),
                    Layout::for_value(&*self.ptr.as_ptr()),
                );
            }
        }
    }

    impl<T: ?Sized, A: Alloc<O> + ?Sized, O: Error> Deref for AllocGuard<'_, T, A, O> {
        type Target = NonNull<T>;

        fn deref(&self) -> &Self::Target {
            &self.ptr
        }
    }

    /// A RAII guard for a heap‐allocated slice that tracks how many elements have been initialized.
    ///
    /// On drop, it will:
    /// 1. Run destructors for each initialized element.
    /// 2. Deallocate the entire slice memory.
    ///
    /// Use [`init`](SliceAllocGuard::init) or [`init_unchecked`](SliceAllocGuard::init_unchecked)
    /// to initialize elements one by one, [`extend_init`](SliceAllocGuard::extend_init) to
    /// initialize many elements at once, and [`release`](SliceAllocGuard::release) to take
    /// ownership of the fully‐initialized slice without running cleanup.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::ptr::NonNull;
    /// # use memapi::{helpers::SliceAllocGuard, Alloc, DefaultAlloc};
    /// # let alloc = DefaultAlloc;
    /// # let len = 5;
    /// let mut guard = SliceAllocGuard::new(
    ///     alloc.alloc_slice::<u32>(len).unwrap().cast::<u32>(),
    ///     &alloc,
    ///     len
    /// );
    ///
    /// for i in 0..len {
    ///     guard.init(i as u32).unwrap();
    /// }
    ///
    /// // All elements are now initialized; take ownership:
    /// // (commented out for this example as the pointer will not be used)
    /// // let slice_ptr = guard.release();
    /// ```
    pub struct SliceAllocGuard<'a, T, A: Alloc + ?Sized> {
        ptr: NonNull<T>,
        alloc: &'a A,
        init: usize,
        full: usize,
    }

    impl<'a, T, A: Alloc + ?Sized> SliceAllocGuard<'a, T, A> {
        /// Creates a new slice guard for `full` elements at `ptr` in the given allocator.
        #[inline]
        pub const fn new(ptr: NonNull<T>, alloc: &'a A, full: usize) -> SliceAllocGuard<'a, T, A> {
            SliceAllocGuard {
                ptr,
                alloc,
                init: 0,
                full,
            }
        }

        /// Release ownership of the slice without deallocating memory.
        #[inline]
        #[must_use]
        pub const fn release(self) -> NonNull<[T]> {
            let ret = NonNull::slice_from_raw_parts(self.ptr, self.init);
            forget(self);
            ret
        }

        /// Initializes the next element of the slice with `elem`.
        ///
        /// # Errors
        ///
        /// Returns `Err(elem)` if the slice is at capacity.
        #[inline]
        pub const fn init(&mut self, elem: T) -> Result<(), T> {
            if self.init == self.full {
                return Err(elem);
            }
            unsafe {
                self.init_unchecked(elem);
            }
            Ok(())
        }

        /// Initializes the next element of the slice with `elem`.
        ///
        /// # Safety
        ///
        /// The caller must ensure that the slice is not at capacity. (`initialized() < full()`)
        #[inline]
        pub const unsafe fn init_unchecked(&mut self, elem: T) {
            self.ptr.add(self.init).write(elem);
            self.init += 1;
        }

        /// Initializes the next elements of the slice with the elements from `iter`.
        ///
        /// # Errors
        ///
        /// Returns `Err((iter, elem))` if the slice is filled before iteration finishes. The
        /// contained iterator will have been partially consumed.
        #[inline]
        pub fn extend_init<I: IntoIterator<Item = T>>(
            &mut self,
            iter: I,
        ) -> Result<(), I::IntoIter> {
            let mut iter = iter.into_iter();
            loop {
                if self.init == self.full {
                    return Err(iter);
                }
                match iter.next() {
                    Some(elem) => unsafe {
                        self.ptr.add(self.init).write(elem);
                        self.init += 1;
                    },
                    None => return Ok(()),
                }
            }
        }

        /// Returns how many elements have been initialized.
        #[inline]
        #[allow(clippy::must_use_candidate)]
        pub const fn initialized(&self) -> usize {
            self.init
        }

        /// Returns the total number of elements in the slice.
        #[inline]
        #[allow(clippy::must_use_candidate)]
        pub const fn full(&self) -> usize {
            self.full
        }

        /// Returns `true` if every element in the slice has been initialized.
        #[inline]
        #[allow(clippy::must_use_candidate)]
        pub const fn is_full(&self) -> bool {
            self.init == self.full
        }

        /// Copies as many elements from `slice` as will fit.
        ///
        /// On success, all elements are copied and `Ok(())` is returned. If
        /// `slice.len() > remaining_capacity`, it copies as many elements as will fit, advances
        /// the initialized count to full, and returns `Err(excess)`.
        ///
        /// # Errors
        ///
        /// Returns `Err(excess)` if `slice.len() > remaining_capacity`.
        pub fn copy_from_slice(&mut self, slice: &[T]) -> Result<(), usize>
        where
            T: Copy,
        {
            let to_copy = slice.len().min(self.full - self.init);

            unsafe {
                slice
                    .as_ptr()
                    .copy_to_nonoverlapping(self.ptr.as_ptr().add(self.init), to_copy);
            }

            self.init += to_copy;
            let uncopied = slice.len() - to_copy;
            if uncopied == 0 {
                Ok(())
            } else {
                Err(uncopied)
            }
        }
    }

    impl<T, A: Alloc + ?Sized> Drop for SliceAllocGuard<'_, T, A> {
        fn drop(&mut self) {
            unsafe {
                NonNull::slice_from_raw_parts(self.ptr, self.init).drop_in_place();
                self.alloc.dealloc_n(self.ptr, self.full);
            }
        }
    }

    impl<T, A: Alloc + ?Sized> Deref for SliceAllocGuard<'_, T, A> {
        type Target = NonNull<T>;

        fn deref(&self) -> &Self::Target {
            &self.ptr
        }
    }
}
