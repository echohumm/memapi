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
//! # use memapi::{Alloc, DefaultAlloc, AllocError};
//! # use core::alloc::Layout;
//! # use core::ptr::NonNull;
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

// TODO: add support for more allocators from external crates

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "metadata", feature(ptr_metadata))]
#![cfg_attr(feature = "clone_to_uninit", feature(clone_to_uninit))]
#![allow(unsafe_op_in_unsafe_fn)]
#![deny(missing_docs)]

extern crate alloc;

#[cfg(feature = "alloc_ext")]
mod alloc_ext;
#[cfg(feature = "resize_in_place")]
mod in_place;

#[cfg(feature = "alloc_ext")]
pub use alloc_ext::*;
#[cfg(feature = "resize_in_place")]
pub use in_place::*;

mod marker;
mod type_props;

/// Small alternatives to Rust functions which are currently unstable.
pub mod unstable_util;

#[cfg(feature = "stats")]
/// Allocation statistic gathering and reporting.
pub mod stats;

pub use marker::*;
pub use type_props::*;

use crate::helpers::layout_or_sz_align;
use core::{
    alloc::{GlobalAlloc, Layout},
    cmp::Ordering,
    error::Error,
    fmt::{self, Display, Formatter},
    ptr::{NonNull, null_mut},
};

/// Helpers which tend to be useful in other libraries as well.
pub mod helpers {
    use crate::Alloc;
    use core::mem::forget;
    use core::{alloc::Layout, ops::Deref, ptr::NonNull};

    /// Gets either a valid layout with space for `n` count of `T`, or a raw size and alignment.
    ///
    /// # Errors
    ///
    /// Returns `Err(size, align)` if creation of a layout with the given size and alignment fails.
    #[inline]
    pub const fn layout_or_sz_align<T>(n: usize) -> Result<Layout, (usize, usize)> {
        let (sz, align) = (size_of::<T>(), align_of::<T>());

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
    /// goes out of scope, it will:
    /// 1. Drop the value of type `T` at the pointer.
    /// 2. Deallocate the underlying memory via the allocator.
    ///
    /// To take ownership of the allocation without deallocating, call
    /// [`release`](SliceAllocGuard::release), which returns the raw pointer and prevents the guard
    /// from running its cleanup.
    ///
    /// This should be used in any situation where the initialization of a pointer's data may panic.
    /// (e.g., initializing via a clone or other user-implemented method)
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
    pub struct AllocGuard<'a, T: ?Sized, A: Alloc + ?Sized> {
        ptr: NonNull<T>,
        alloc: &'a A,
    }

    impl<'a, T: ?Sized, A: Alloc + ?Sized> AllocGuard<'a, T, A> {
        /// Creates a new guard from a pointer and a reference to an allocator.
        #[inline]
        pub const fn new(ptr: NonNull<T>, alloc: &'a A) -> AllocGuard<'a, T, A> {
            AllocGuard { ptr, alloc }
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

    impl<T: ?Sized, A: Alloc + ?Sized> Drop for AllocGuard<'_, T, A> {
        fn drop(&mut self) {
            unsafe {
                self.alloc.dealloc(
                    self.ptr.cast::<u8>(),
                    Layout::for_value(&*self.ptr.as_ptr()),
                );
            }
        }
    }

    impl<T: ?Sized, A: Alloc + ?Sized> Deref for AllocGuard<'_, T, A> {
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

/// Default allocator, delegating to the global allocator.
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefaultAlloc;

/// A memory allocation interface.
///
/// This trait does _not_ require `Self: Allocator` and is `no_std`-compatible.
pub trait Alloc {
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// Returns a non-null pointer on success, or [`AllocError::AllocFailed`].
    #[track_caller]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError>;

    /// Attempts to allocate a block of memory for `len` instances of `T`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    fn alloc_slice<T>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
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
    /// Returns a non-null pointer on success, or [`AllocError::AllocFailed`].
    #[track_caller]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError>;

    /// Attempts to allocate a zeroed block of memory for `len` instances of `T`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    fn alloc_slice_zeroed<T>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
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
    /// Returns a non-null pointer on success, or [`AllocError::AllocFailed`].
    #[track_caller]
    fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError>;

    /// Attempts to allocate a block of memory for `len` instances of `T`, filled with bytes
    /// initialized to `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    fn alloc_slice_filled<T>(&self, len: usize, n: u8) -> Result<NonNull<[T]>, AllocError> {
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
    /// Returns [`AllocError::AllocFailed`] if the allocation fails.
    #[track_caller]
    fn alloc_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError>;

    /// Attempts to allocate a block of memory for `len` instances of `T` and
    /// fill it by calling `pattern(i)` for each byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    fn alloc_slice_patterned<T, F: Fn(usize) -> u8 + Clone>(
        &self,
        len: usize,
        pattern: F,
    ) -> Result<NonNull<[T]>, AllocError> {
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
    ) -> Result<NonNull<u8>, AllocError> {
        grow(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::None,
        )
    }

    /// Grows the given block to a new, larger layout, zeroing newly allocated space.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] in `new_layout.size() < old_layout.size()`.
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
    ) -> Result<NonNull<u8>, AllocError> {
        grow(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::Zero,
        )
    }

    /// Grow the given block to a new, larger layout, filling any newly allocated
    /// bytes by calling `pattern(i)` for each new byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_layout.size() < old_layout.size()`.
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
    ) -> Result<NonNull<u8>, AllocError> {
        grow(self, ptr, old_layout, new_layout, AllocPattern::Fn(pattern))
    }

    /// Grows the given block to a new, larger layout, filling newly allocated space with `n`.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] in `new_layout.size() < old_layout.size()`.
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
    ) -> Result<NonNull<u8>, AllocError> {
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
    ) -> Result<NonNull<u8>, AllocError> {
        shrink(self, ptr, old_layout, new_layout)
    }

    /// Reallocate a block, growing or shrinking as needed (no zeroing).
    ///
    /// On grow, preserves existing contents up to `old_layout.size()`, and
    /// on shrink, truncates to `new_layout.size()`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
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
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.size() > old_layout.size() {
            grow_unchecked(
                self,
                ptr,
                old_layout,
                new_layout,
                AllocPattern::<fn(usize) -> u8>::None,
            )
        } else {
            shrink_unchecked(self, ptr, old_layout, new_layout)
        }
    }

    /// Reallocate a block, growing or shrinking as needed, zeroing any newly
    /// allocated bytes.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
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
    ) -> Result<NonNull<u8>, AllocError> {
        self.realloc_filled(ptr, old_layout, new_layout, 0)
    }

    /// Reallocate a block, growing or shrinking as needed, filling any new
    /// bytes by calling `pattern(i)` for each new byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
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
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.size() > old_layout.size() {
            grow_unchecked(self, ptr, old_layout, new_layout, AllocPattern::Fn(pattern))
        } else {
            shrink_unchecked(self, ptr, old_layout, new_layout)
        }
    }

    /// Reallocate a block, growing or shrinking as needed, filling any newly
    /// allocated bytes with `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
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
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.size() > old_layout.size() {
            grow_unchecked(
                self,
                ptr,
                old_layout,
                new_layout,
                AllocPattern::<fn(usize) -> u8>::All(n),
            )
        } else {
            shrink_unchecked(self, ptr, old_layout, new_layout)
        }
    }
}

#[cfg(feature = "nightly")]
/// The primary module for when `nightly` is enabled.
pub(crate) mod nightly {
    use super::{Alloc, AllocError, DefaultAlloc};
    use crate::helpers::AllocGuard;
    use alloc::alloc::{Allocator, Global, Layout};
    use core::ptr::NonNull;

    unsafe impl Allocator for DefaultAlloc {
        #[track_caller]
        #[inline]
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
            Allocator::allocate(&Global, layout)
        }

        #[track_caller]
        #[inline]
        fn allocate_zeroed(
            &self,
            layout: Layout,
        ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
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
        ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
            Allocator::grow(&Global, ptr.cast(), old_layout, new_layout)
        }

        #[track_caller]
        #[inline]
        unsafe fn grow_zeroed(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
            Allocator::grow_zeroed(&Global, ptr.cast(), old_layout, new_layout)
        }

        #[track_caller]
        #[inline]
        unsafe fn shrink(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
            Allocator::shrink(&Global, ptr.cast(), old_layout, new_layout)
        }
    }

    macro_rules! default_alloc_impl {
        ($ty:ty) => {
            impl Alloc for $ty {
                #[track_caller]
                #[inline]
                fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
                    Allocator::allocate(self, layout)
                        .map_err(|_| AllocError::AllocFailed(layout))
                        .map(NonNull::cast)
                }

                #[track_caller]
                #[inline]
                fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
                    Allocator::allocate_zeroed(self, layout)
                        .map_err(|_| AllocError::AllocFailed(layout))
                        .map(NonNull::cast)
                }

                #[track_caller]
                #[inline]
                fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError> {
                    Allocator::allocate(self, layout)
                        .map_err(|_| AllocError::AllocFailed(layout))
                        .map(|ptr| {
                            let ptr = ptr.cast::<u8>();
                            unsafe {
                                ptr.write_bytes(n, layout.size());
                            }
                            ptr
                        })
                }

                #[track_caller]
                #[inline]
                fn alloc_patterned<F: Fn(usize) -> u8 + Clone>(
                    &self,
                    layout: Layout,
                    pattern: F,
                ) -> Result<NonNull<u8>, AllocError> {
                    Allocator::allocate(self, layout)
                        .map_err(|_| AllocError::AllocFailed(layout))
                        .map(|ptr| {
                            let guard = AllocGuard::new(ptr.cast::<u8>(), self);
                            for i in 0..layout.size() {
                                unsafe {
                                    guard.as_ptr().add(i).write(pattern(i));
                                }
                            }
                            guard.release()
                        })
                }

                #[track_caller]
                #[inline]
                unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
                    Allocator::deallocate(self, ptr.cast(), layout);
                }
            }
        };
    }

    default_alloc_impl!(DefaultAlloc);
    default_alloc_impl!(Global);
    #[cfg(feature = "std")]
    default_alloc_impl!(std::alloc::System);

    impl<A: Alloc + ?Sized> Alloc for &A {
        #[track_caller]
        #[inline]
        fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
            (**self).alloc(layout)
        }

        #[track_caller]
        #[inline]
        fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
            (**self).alloc_zeroed(layout)
        }

        #[track_caller]
        #[inline]
        fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError> {
            (**self).alloc_filled(layout, n)
        }

        #[track_caller]
        #[inline]
        fn alloc_patterned<F: Fn(usize) -> u8 + Clone>(
            &self,
            layout: Layout,
            pattern: F,
        ) -> Result<NonNull<u8>, AllocError> {
            (**self).alloc_patterned(layout, pattern)
        }

        #[track_caller]
        #[inline]
        unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
            (**self).dealloc(ptr, layout);
        }
    }
}

#[cfg(not(feature = "nightly"))]
/// The fallback module for stable Rust.
pub(crate) mod fallback {
    use super::{Alloc, AllocError};
    use crate::helpers::AllocGuard;
    use alloc::alloc::{
        Layout, alloc as raw_alloc, alloc_zeroed as raw_alloc_zeroed, dealloc as raw_dealloc,
    };
    use core::ptr::NonNull;

    impl Alloc for super::DefaultAlloc {
        #[track_caller]
        #[inline]
        fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
            NonNull::new(unsafe { raw_alloc(layout) }).ok_or(AllocError::AllocFailed(layout))
        }

        #[track_caller]
        #[inline]
        fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
            NonNull::new(unsafe { raw_alloc_zeroed(layout) }).ok_or(AllocError::AllocFailed(layout))
        }

        #[track_caller]
        #[inline]
        fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError> {
            let ptr = NonNull::new(unsafe { raw_alloc(layout).cast::<u8>() })
                .ok_or(AllocError::AllocFailed(layout))?;
            unsafe {
                ptr.write_bytes(n, layout.size());
            }
            Ok(ptr)
        }

        #[track_caller]
        #[inline]
        fn alloc_patterned<F: Fn(usize) -> u8 + Clone>(
            &self,
            layout: Layout,
            pattern: F,
        ) -> Result<NonNull<u8>, AllocError> {
            let guard = AllocGuard::new(
                NonNull::new(unsafe { raw_alloc(layout).cast::<u8>() })
                    .ok_or(AllocError::AllocFailed(layout))?,
                self,
            );
            for i in 0..layout.size() {
                unsafe {
                    guard.as_ptr().add(i).write(pattern(i));
                }
            }
            Ok(guard.release())
        }

        #[track_caller]
        #[inline]
        unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
            raw_dealloc(ptr.as_ptr(), layout);
        }
    }

    impl<A: Alloc + ?Sized> Alloc for &A {
        fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
            (*self).alloc(layout)
        }

        fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
            (*self).alloc_zeroed(layout)
        }

        fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError> {
            (*self).alloc_filled(layout, n)
        }

        fn alloc_patterned<F: Fn(usize) -> u8 + Clone>(
            &self,
            layout: Layout,
            pattern: F,
        ) -> Result<NonNull<u8>, AllocError> {
            (*self).alloc_patterned(layout, pattern)
        }

        unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
            (*self).dealloc(ptr, layout);
        }
    }
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

/// Errors for allocation operations.
#[derive(Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum AllocError {
    /// A basic arithmetic operation overflowed.
    ArithmeticOverflow,
    /// The layout computed with the given size and alignment is invalid.
    LayoutError(usize, usize),
    /// The underlying allocator failed to allocate using the given layout.
    AllocFailed(Layout),
    /// Attempted to grow to a smaller layout.
    GrowSmallerNewLayout(usize, usize),
    /// Attempted to shrink to a larger layout.
    ShrinkBiggerNewLayout(usize, usize),
    #[cfg(feature = "resize_in_place")]
    /// Resizing in-place was found to be impossible.
    // Note that this variant means the allocator supports resizing in-place, but it failed.
    CannotResizeInPlace,
}

impl Display for AllocError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AllocError::ArithmeticOverflow => write!(f, "arithmetic overflow"),
            AllocError::LayoutError(sz, align) => {
                write!(f, "computed invalid layout: size: {sz}, align: {align}")
            }
            AllocError::AllocFailed(l) => write!(f, "allocation failed for layout: {l:?}"),
            AllocError::GrowSmallerNewLayout(old, new) => write!(
                f,
                "attempted to grow from a size of {old} to a smaller size of {new}"
            ),
            AllocError::ShrinkBiggerNewLayout(old, new) => write!(
                f,
                "attempted to shrink from a size of {old} to a larger size of {new}"
            ),
            #[cfg(feature = "resize_in_place")]
            AllocError::CannotResizeInPlace => write!(f, "cannot resize in place"),
        }
    }
}

impl Error for AllocError {}

/// Internal helper to grow the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`, filling new bytes using `pattern.`
#[inline]
#[track_caller]
fn grow<A: Alloc + ?Sized, F: Fn(usize) -> u8 + Clone>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError> {
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
fn shrink<A: Alloc + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> Result<NonNull<u8>, AllocError> {
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
unsafe fn grow_unchecked<A: Alloc + ?Sized, F: Fn(usize) -> u8 + Clone>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError> {
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
unsafe fn shrink_unchecked<A: Alloc + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> Result<NonNull<u8>, AllocError> {
    let new_ptr = a.alloc(new_layout)?.cast::<u8>();
    unsafe {
        ptr.copy_to_nonoverlapping(new_ptr, new_layout.size());
        a.dealloc(ptr, old_layout);
    }
    Ok(new_ptr)
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
