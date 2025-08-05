//! `memapi` provides a minimal, `no_std`-friendly memory allocation interface
//! for managing raw buffers, suitable for use in collections.
// TODO: complete these docs again (here and in helpers' SliceAllocGuard)
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

#![allow(clippy::ptr_as_ptr)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "metadata", feature(ptr_metadata))]
#![cfg_attr(feature = "clone_to_uninit", feature(clone_to_uninit))]
#![cfg_attr(feature = "specialization", feature(min_specialization))]
#![cfg_attr(feature = "sized_hierarchy", feature(sized_hierarchy))]
#![allow(unknown_lints, unsafe_op_in_unsafe_fn, internal_features)]
#![deny(missing_docs)]

// TODO: less inlining
// TODO: get rid of all placeholders (like in docs)

// TODO: generally add more helpers and dedup to reduce bin size


// TODO: collapse this into fewer branches
macro_rules! const_if {
    (
        $feature:literal,
        $docs:literal,
        $(#[$attr:meta])*
        // this is also pretty poorly done, but it makes type param and optional req work
        pub const fn $name:ident $(<$generic_ty:ident $(: $req:ident)?>)? ( $($args:tt)* )
        $(-> $ret:ty)?
        // also kinda poorly done, but it makes a single where clause work
        $(where $where_ty:ident : $where_req:ident)?
        $body:block
    ) => {
        // when the feature is enabled, emit a `const fn`
        #[cfg(feature = $feature)]
        #[doc = $docs]
        // feature should only be enabled on compatible versions, so we allow this
        #[allow(clippy::incompatible_msrv)]
        $(#[$attr])*
        pub const fn $name $(<$generic_ty $(: $req)?>)? ($($args)*)
        $(-> $ret)? $(where $where_ty: $where_req)? $body

        // when the feature is disabled, drop the `const`
        #[cfg(not(feature = $feature))]
        #[doc = $docs]
        $(#[$attr])*
        pub fn $name $(<$generic_ty $(: $req)?>)? ($($args)*)
        $(-> $ret)? $(where $where_ty: $where_req)? $body
    };
    // branch for lifetime instead of type param
    (
        $feature:literal,
        $docs:literal,
        $(#[$attr:meta])*
        // this is also pretty poorly done, but it makes type param and optional req work
        pub const fn $name:ident $(<$lt:lifetime>)? ( $($args:tt)* )
        $(-> $ret:ty)?
        $body:block
    ) => {
        #[cfg(feature = $feature)]
        #[doc = $docs]
        #[allow(clippy::incompatible_msrv)]
        $(#[$attr])*
        pub const fn $name $(<$lt>)? ($($args)*)
        $(-> $ret)? $body

        #[cfg(not(feature = $feature))]
        #[doc = $docs]
        $(#[$attr])*
        pub fn $name $(<$lt>)? ($($args)*) $(-> $ret)? $body
    };
    // branch for unsafe functions
    (
        $feature:literal,
        $docs:literal,
        $(#[$attr:meta])*
        //                                kinda poorly done, but it makes a type param work, which
        //                                is all i need.
        pub const unsafe fn $name:ident $(<$generic_ty:ident : $req:ident>)? ( $($args:tt)* )
        $(-> $ret:ty)?
        $body:block
    ) => {
        #[cfg(feature = $feature)]
        #[doc = $docs]
        #[allow(clippy::incompatible_msrv)]
        $(#[$attr])*
        pub const unsafe fn $name$(<$generic_ty: $req>)?($($args)*) $(-> $ret)? $body

        #[cfg(not(feature = $feature))]
        #[doc = $docs]
        $(#[$attr])*
        pub unsafe fn $name$(<$generic_ty: $req>)?($($args)*) $(-> $ret)? $body
    };
}

extern crate alloc;
extern crate core;

#[cfg(feature = "external_alloc")]
pub(crate) mod external_alloc;

#[cfg(any(
    feature = "alloc_ext",
    feature = "alloc_slice",
    feature = "owned",
    feature = "resize_in_place",
    feature = "stats"
))]
mod features;

#[cfg(any(feature = "owned", feature = "stats"))]
pub use features::*;

#[cfg(feature = "alloc_ext")]
pub use features::alloc_ext::*;
#[cfg(feature = "alloc_slice")]
pub use features::alloc_slice::*;
#[cfg(feature = "resize_in_place")]
pub use features::resize_in_place::*;

#[cfg(feature = "external_alloc")]
pub use external_alloc::*;

/// Marker traits.
pub mod marker;
/// Sized type properties as constants and property getters for pointers.
pub mod type_props;

/// Small alternatives to Rust functions which are currently unstable.
pub mod unstable_util;

/// Errors which can occur during allocation.
pub mod error;

use alloc::alloc::{
    alloc as raw_all, alloc_zeroed as raw_allz, dealloc as de, GlobalAlloc, Layout,
};
use core::{
    cmp::Ordering,
    ptr::{self, null_mut, NonNull},
};
use {error::AllocError, helpers::null_q_zsl_check};

/// Default allocator, delegating to the global allocator.
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefaultAlloc;

macro_rules! default_alloc_impl {
    ($ty:ty) => {
        impl Alloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
                null_q_zsl_check(layout, |layout| unsafe { raw_all(layout) })
            }

            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
                null_q_zsl_check(layout, |layout| unsafe { raw_allz(layout) })
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
                    ptr::write_bytes(p.as_ptr(), 0, layout.size());
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

    /// Reallocates a block, growing or shrinking as needed.
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

    /// Reallocates a block, growing or shrinking as needed, zeroing any newly
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
    use crate::{error::AllocError, helpers::null_q_zsl_check, Alloc, DefaultAlloc};
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
    helpers::zsl_check(layout, |layout: Layout| {
        helpers::null_q(unsafe { alloc(a, layout) }, layout)
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
        Ordering::Less => grow_unchecked(a, ptr, old_layout, new_layout, pattern),
        Ordering::Equal => {
            if new_layout.align() == old_layout.align() {
                Ok(ptr)
            } else {
                grow_unchecked(&a, ptr, old_layout, new_layout, pattern)
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
                shrink_unchecked(&a, ptr, old_layout, new_layout)
            }
        }
        Ordering::Greater => shrink_unchecked(a, ptr, old_layout, new_layout),
    }
}

/// Internal helper to grow the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
///
/// # Safety
///
/// This function does not check for layout validity. `new_layout.size()` should be greater than
/// `old_layout.size()`.
#[allow(clippy::needless_pass_by_value)]
#[inline]
#[cfg_attr(miri, track_caller)]
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

    ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_layout.size());
    a.dealloc(ptr, old_layout);

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

    ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_layout.size());
    a.dealloc(ptr, old_layout);

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
        Ordering::Less => grow_unchecked(&a, ptr, old_layout, new_layout, pat),
        Ordering::Greater => shrink_unchecked(&a, ptr, old_layout, new_layout),
        Ordering::Equal => {
            if new_layout.align() == old_layout.align() {
                Ok(ptr)
            } else {
                grow_unchecked(&a, ptr, old_layout, new_layout, pat)
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
pub mod helpers;
