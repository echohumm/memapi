//! `memapi` provides a minimal, `no_std`-friendly memory allocation interface
//! for managing raw buffers, suitable for use in collections.
// //! This crate exports:
// //!
// //! - [`Alloc`], a trait defining basic allocate, deallocate, grow, and shrink operations.
// //! - [`DefaultAlloc`], a zero-cost wrapper delegating to the global allocator.
// //! - [`AllocError`], an enum of possible error cases.
// //!
// //! - [`PtrProps`](PtrProps), properties getters for pointers to values.
// //! - [`SizedProps`], properties for sized types. Similar to the unstable
// //!   [`SizedTypeProperties`](core::mem::SizedTypeProperties).
// //!
// //! - [`UnsizedCopy`], a marker trait indicating a value can be copied safely even if unsized.
// //! - [`Thin`], a marker trait indicating a pointer to a type has no metadata.
// //!
// //! And, if the `alloc_ext` feature is on:
// //!
// //! - `AllocExt`, defining abstractions over Alloc's API.
// //!
// //! # Examples
// //!
// //! ```rust
// //! # use memapi::{Alloc, DefaultAlloc, error::AllocError};
// //! # use core::{
// //! #    alloc::Layout,
// //! #    ptr::NonNull
// //! # };
// //! let allocator = DefaultAlloc;
// //! // Allocate 4 usizes.
// //! let ptr = allocator.alloc_slice::<usize>(4).expect("alloc failed").cast::<usize>();
// //! unsafe {
// //!     for i in 0..4 {
// //!         ptr.add(i).write(17384 * i + 8923)
// //!     }
// //! }
// //! // Deallocate the block.
// //! unsafe { allocator.dealloc_n(ptr, 4) };
// //! ```

// maybedo: maybe update the readme and the docs above

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "metadata", feature(ptr_metadata))]
#![cfg_attr(feature = "clone_to_uninit", feature(clone_to_uninit))]
#![cfg_attr(feature = "specialization", feature(min_specialization))]
#![cfg_attr(feature = "sized_hierarchy", feature(sized_hierarchy))]
#![allow(unsafe_op_in_unsafe_fn, internal_features)]
#![deny(missing_docs)]

// it is used, the compiler is just stupid
#[allow(unused_macros)]
macro_rules! realloc {
    ($fun:ident, $self:ident, $ptr:ident, $len:expr, $new_len:expr, $ty:ty $(,$pat:ident$(($val:ident))?)?) => {
		realloc!(fn(usize) -> u8, $fun, $self, $ptr, $len, $new_len, $ty $(,$pat$(($val))?)?)
	};
    ($f:ty, $fun:ident, $self:ident, $ptr:ident, $len:expr, $new_len:expr, $ty:ty $(,$pat:ident$(($val:ident))?)?) => {
        $fun(
            $self,
            $ptr.cast(),
            Layout::from_size_align_unchecked($len * <$ty>::SZ, <$ty>::ALIGN),
            layout_or_sz_align::<$ty>($new_len)
                .map_err(|(sz, aln)| AllocError::LayoutError(sz, aln))?,
            $(AllocPattern::<$f>::$pat$(($val))?)?
        )
        .map(NonNull::cast)
    }
}

extern crate alloc;
extern crate core;

#[cfg(feature = "alloc_ext")]
pub use alloc_ext::*;
#[cfg(feature = "resize_in_place")]
pub use in_place::*;

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
    helpers::{null_q, zsl_check},
};
use alloc::alloc::{
    alloc as raw_all, alloc_zeroed as raw_allz, dealloc as de, GlobalAlloc, Layout,
};
use core::{
    cmp::Ordering,
    ptr::{null_mut, NonNull},
};

/// Default allocator, delegating to the global allocator.
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefaultAlloc;

macro_rules! default_alloc_impl {
    ($ty:ty) => {
        impl Alloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
                zsl_check(layout, |layout| null_q(unsafe { raw_all(layout) }, layout))
            }

            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
                zsl_check(layout, |layout| null_q(unsafe { raw_allz(layout) }, layout))
            }

            #[cfg_attr(miri, track_caller)]
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
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        match Alloc::alloc(&self, layout) {
            Ok(ptr) => ptr.as_ptr(),
            Err(_) => null_mut(),
        }
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        Alloc::dealloc(&self, NonNull::new_unchecked(ptr), layout);
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        match Alloc::alloc_zeroed(&self, layout) {
            Ok(ptr) => ptr.as_ptr(),
            Err(_) => null_mut(),
        }
    }

    #[cfg_attr(miri, track_caller)]
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
pub trait Alloc {
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError>;

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
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

    /// Deallocates a previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `layout` must describe exactly the same block.
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout);

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
    #[cfg_attr(miri, track_caller)]
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
    #[cfg_attr(miri, track_caller)]
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
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
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
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
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
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        ralloc(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::Zero,
        )
    }
}

#[cfg(feature = "nightly")]
/// The primary module for when `nightly` is enabled.
pub(crate) mod nightly {
    use crate::{
        error::AllocError,
        helpers::{null_q, zsl_check},
        Alloc, DefaultAlloc,
    };
    use alloc::alloc::{
        alloc as raw_all, alloc_zeroed as raw_allz, dealloc as de, Allocator, Global, Layout,
    };
    use core::{alloc::AllocError as AllocatorError, ptr::NonNull};

    unsafe impl Allocator for DefaultAlloc {
        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocatorError> {
            Allocator::allocate(&Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocatorError> {
            Allocator::allocate_zeroed(&Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            Allocator::deallocate(&Global, ptr.cast(), layout);
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocatorError> {
            Allocator::grow(&Global, ptr.cast(), old_layout, new_layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow_zeroed(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocatorError> {
            Allocator::grow_zeroed(&Global, ptr.cast(), old_layout, new_layout)
        }

        #[cfg_attr(miri, track_caller)]
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

impl<A: Alloc + ?Sized> Alloc for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        (**self).alloc(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        (**self).alloc_zeroed(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        (**self).dealloc(ptr, layout);
    }
}

#[cfg(feature = "std")]
#[cfg_attr(miri, track_caller)]
#[inline]
fn zsl_check_alloc<A: GlobalAlloc>(
    a: &A,
    layout: Layout,
    alloc: unsafe fn(&A, Layout) -> *mut u8,
) -> Result<NonNull<u8>, AllocError> {
    zsl_check(layout, |layout: Layout| {
        null_q(unsafe { alloc(a, layout) }, layout)
    })
}

#[cfg(feature = "std")]
impl Alloc for std::alloc::System {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zsl_check_alloc(self, layout, GlobalAlloc::alloc)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zsl_check_alloc(self, layout, GlobalAlloc::alloc_zeroed)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        GlobalAlloc::dealloc(self, ptr.as_ptr(), layout);
    }
}

/// Internal helper to grow the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`, filling new bytes using `pattern.`
#[inline]
#[cfg_attr(miri, track_caller)]
pub(crate) unsafe fn grow<A: Alloc + ?Sized, F: Fn(usize) -> u8 + Clone>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => unsafe { grow_unchecked(a, ptr, old_layout, new_layout, pattern) },
        Ordering::Equal => {
            if new_layout.align() == old_layout.align() {
                Ok(ptr)
            } else {
                unsafe { grow_unchecked(&a, ptr, old_layout, new_layout, pattern) }
            }
        }
        Ordering::Greater => Err(AllocError::GrowSmallerNewLayout(
            old_layout.size(),
            new_layout.size(),
        )),
    }
}

/// Internal helper to shrink the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
#[inline]
#[cfg_attr(miri, track_caller)]
pub(crate) unsafe fn shrink<A: Alloc + ?Sized>(
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
        Ordering::Equal => {
            if new_layout.align() == old_layout.align() {
                Ok(ptr)
            } else {
                unsafe { shrink_unchecked(&a, ptr, old_layout, new_layout) }
            }
        }
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
#[cfg_attr(miri, track_caller)]
#[allow(clippy::needless_pass_by_value)]
unsafe fn grow_unchecked<A: Alloc + ?Sized, F: Fn(usize) -> u8 + Clone>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError> {
    let new_ptr = match pattern {
        AllocPattern::None => a.alloc(new_layout)?.cast::<u8>(),
        #[cfg(feature = "alloc_ext")]
        AllocPattern::Fn(f) => a.alloc_patterned(new_layout, f)?,
        AllocPattern::Zero => a.alloc_zeroed(new_layout)?.cast::<u8>(),
        #[cfg(feature = "alloc_ext")]
        AllocPattern::All(n) => a.alloc_filled(new_layout, n)?.cast::<u8>(),
        #[cfg(not(feature = "alloc_ext"))]
        AllocPattern::PhantomFn(_) => {
            unreachable!("if this is reached, somebody did something really wrong")
        }
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
#[cfg_attr(miri, track_caller)]
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

/// Helper for realloc to reduce repetition.
#[cfg_attr(miri, track_caller)]
#[inline]
pub(crate) unsafe fn ralloc<A: Alloc + ?Sized, F: Fn(usize) -> u8 + Clone>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pat: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => unsafe { grow_unchecked(&a, ptr, old_layout, new_layout, pat) },
        Ordering::Greater => unsafe { shrink_unchecked(&a, ptr, old_layout, new_layout) },
        Ordering::Equal => {
            if new_layout.align() == old_layout.align() {
                Ok(ptr)
            } else {
                unsafe { grow_unchecked(&a, ptr, old_layout, new_layout, pat) }
            }
        }
    }
}

/// The pattern to fill new bytes with.
pub(crate) enum AllocPattern<F: Fn(usize) -> u8 + Clone> {
    /// Don't fill bytes at all.
    None,
    /// Zero all bytes.
    Zero,
    #[cfg(feature = "alloc_ext")]
    /// Set all bytes to a specific value.
    All(u8),
    #[cfg(feature = "alloc_ext")]
    /// Get the value of the byte using the given predicate.
    Fn(F),
    #[cfg(not(feature = "alloc_ext"))]
    #[allow(dead_code)]
    PhantomFn(core::marker::PhantomData<F>),
}

/// Helpers which tend to be useful in other libraries as well.
pub mod helpers {
    #[allow(unused_imports)]
    // once again, this is used; the compiler is just stupid
    use crate::{
        error::AllocError,
        shrink,
        type_props::{PtrProps, SizedProps},
        Alloc,
    };
    use core::{
        alloc::Layout,
        mem::{forget, transmute},
        num::NonZeroUsize,
        ops::Deref,
        ptr::{eq as peq, NonNull},
    };

    // yet again.
    #[allow(dead_code)]
    pub(crate) const TRUNC_LGR: &str = "attempted to truncate a slice to a larger size";

    /// Converts a possibly null pointer into a [`NonNull`] result.
    #[inline]
    pub(crate) const fn null_q<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        if ptr.is_null() {
            Err(AllocError::AllocFailed(layout))
        } else {
            Ok(unsafe { NonNull::new_unchecked(ptr.cast()) })
        }
    }

    /// Checks layout for being zero-sized, returning an error if it is.
    #[inline]
    pub(crate) fn zsl_check<Ret, F: Fn(Layout) -> Result<Ret, AllocError>>(
        layout: Layout,
        ret: F,
    ) -> Result<Ret, AllocError> {
        if layout.size() == 0 {
            Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
        } else {
            ret(layout)
        }
    }

    #[cfg(any(feature = "alloc_slice", feature = "owned"))]
    /// Deallocates `n` elements of type `T` at `ptr` using a reference to an `A`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub(crate) unsafe fn dealloc_n<T, A: Alloc + ?Sized>(a: &A, ptr: NonNull<T>, n: usize) {
        // Here, we assume the layout is valid as it was presumably used to allocate previously.
        a.dealloc(
            ptr.cast(),
            Layout::from_size_align_unchecked(T::SZ * n, T::ALIGN),
        );
    }

    #[cfg(any(feature = "alloc_slice", feature = "owned"))]
    /// Allocates a slice of `len` elements of type `T` using the given reference to an `A` and an
    /// allocation function pointer.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub(crate) fn alloc_slice<T, A: Alloc + ?Sized>(
        a: &A,
        len: usize,
        alloc: fn(&A, Layout) -> Result<NonNull<u8>, AllocError>,
    ) -> Result<NonNull<[T]>, AllocError> {
        let layout = layout_or_sz_align::<T>(len)
            .map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        alloc(a, layout).map(|ptr| NonNull::slice_from_raw_parts(ptr.cast(), len))
    }

    #[cfg(all(any(feature = "alloc_ext", feature = "owned"), feature = "metadata"))]
    /// Allocates space for a copy of the value behind `data`, and copies it into the new memory.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub(crate) unsafe fn alloc_copy_ptr_to_unchecked<T: ?Sized, A: Alloc + ?Sized>(
        a: &A,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        match a.alloc(data.layout()) {
            Ok(ptr) => Ok({
                NonNull::new_unchecked(data.cast_mut().cast())
                    .copy_to_nonoverlapping(ptr, data.size());
                NonNull::from_raw_parts(ptr, core::ptr::metadata(data))
            }),
            Err(e) => Err(e),
        }
    }

    #[cfg(any(feature = "alloc_ext", feature = "owned"))]
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub(crate) fn alloc_write<T, A: Alloc + ?Sized>(
        a: &A,
        val: T,
    ) -> Result<NonNull<T>, AllocError> {
        match a.alloc(T::LAYOUT) {
            Ok(ptr) => Ok(unsafe {
                let ptr = ptr.cast();
                ptr.write(val);
                ptr
            }),
            Err(e) => Err(e),
        }
    }

    /// Checks equality between two [`NonNull`] pointers.
    #[must_use]
    #[inline]
    pub fn nonnull_eq<T: ?Sized>(a: NonNull<T>, b: NonNull<T>) -> bool {
        peq(a.as_ptr().cast_const(), b.as_ptr().cast_const())
    }

    /// Aligns the given value up to a non-zero alignment.
    #[must_use]
    #[inline]
    pub const fn align_up(n: usize, align: NonZeroUsize) -> usize {
        unsafe { align_up_unchecked(n, align.get()) }
    }

    /// Aligns the given value up to an alignment.
    ///
    /// # Safety
    ///
    /// `align` must be non-zero.
    #[must_use]
    #[inline]
    pub const unsafe fn align_up_unchecked(n: usize, align: usize) -> usize {
        let m1 = unsafe { align.unchecked_sub(1) };
        (n + m1) & !m1
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
    /// The caller must ensure the `alignment` is a valid power of two.
    #[must_use]
    #[inline]
    pub const unsafe fn dangling_nonnull(align: usize) -> NonNull<u8> {
        transmute::<NonZeroUsize, NonNull<u8>>(unsafe { NonZeroUsize::new_unchecked(align) })
    }

    /// Gets either a valid layout with space for `n` count of `T`, or a raw size and alignment.
    ///
    /// # Errors
    ///
    /// Returns `Err(size, align)` if creation of a layout with the given size and alignment fails.
    #[inline]
    pub const fn layout_or_sz_align<T>(n: usize) -> Result<Layout, (usize, usize)> {
        let (sz, align) = (T::SZ, T::ALIGN);

        if sz != 0
            && n > unsafe { (isize::MAX as usize).unchecked_add(1).unchecked_sub(align) } / sz
        {
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

        /// Initializes the value by writing to the contained pointer.
        #[cfg_attr(miri, track_caller)]
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

    impl<T: ?Sized, A: Alloc + ?Sized> Drop for AllocGuard<'_, T, A> {
        #[cfg_attr(miri, track_caller)]
        fn drop(&mut self) {
            unsafe {
                self.alloc.dealloc(self.ptr.cast::<u8>(), self.ptr.layout());
            }
        }
    }

    impl<T: ?Sized, A: Alloc + ?Sized> Deref for AllocGuard<'_, T, A> {
        type Target = NonNull<T>;

        fn deref(&self) -> &NonNull<T> {
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
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// # use core::ptr::NonNull;
    // /// # use memapi::{helpers::SliceAllocGuard, Alloc, DefaultAlloc};
    // /// # let alloc = DefaultAlloc;
    // /// # let len = 5;
    // /// let mut guard = SliceAllocGuard::new(
    // ///     alloc.alloc_slice::<u32>(len).unwrap().cast::<u32>(),
    // ///     &alloc,
    // ///     len
    // /// );
    // ///
    // /// for i in 0..len {
    // ///     guard.init(i as u32).unwrap();
    // /// }
    // ///
    // /// // All elements are now initialized; take ownership:
    // /// // (commented out for this example as the pointer will not be used)
    // /// // let slice_ptr = guard.release();
    // /// ```
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
                self.alloc.dealloc(
                    self.ptr.cast(),
                    Layout::from_size_align_unchecked(T::SZ * self.full, align_of::<T>()),
                );
            }
        }
    }

    impl<T, A: Alloc + ?Sized> Deref for SliceAllocGuard<'_, T, A> {
        type Target = NonNull<T>;

        fn deref(&self) -> &NonNull<T> {
            &self.ptr
        }
    }
}
