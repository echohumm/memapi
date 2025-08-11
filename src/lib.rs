//! `memapi` provides a `no_std`-friendly memory allocation interface
//! for managing raw buffers, suitable for use in collections.
//!
//! This crate exports:
//!
//! - [`Alloc`]: a trait defining basic allocation, deallocation, grow, and shrink operations.
//! - [`DefaultAlloc`]: a zero-cost wrapper delegating to the global allocator.
//! - [`AllocError`]: an enum representing allocation failure cases.
//! - [`PtrProps`](type_props::PtrProps): property getters for pointers to values.
//! - [`SizedProps`](type_props::SizedProps): properties for sized types, similar to the unstable,
//!   hidden [`SizedTypeProperties`](core::mem::SizedTypeProperties).
//! - [`VarSized`](type_props::VarSized): a marker trait for types with `usize` metadata.
//! - [`UnsizedCopy`](marker::UnsizedCopy): a marker trait for safe copying of unsized values.
//! - [`Thin`](marker::Thin): a marker trait for pointers without metadata.
//!
//! # Features
//!
//! - **`alloc_ext`**: Adds the [`AllocExt`] trait for ergonomic allocator abstractions.
//!
//! - **`alloc_slice`**: Provides slice-based extensions:
//!   - [`AllocSlice`] for basic slice operations.
//!   - (with `alloc_ext`) [`AllocSliceExt`] for advanced slice abstractions.
//!
//! - **`stats`**: Collection of allocation statistics utilities:
//!   - [`StatsLogger`], a thread-safe logger for allocation events.
//!   - [`Stats`], an allocator wrapper that logs operations.
//!   - [`AllocRes`], [`AllocStat`], [`MemoryRegion`], [`ResizeMemRegions`], [`AllocKind`] types.
//!   - (With `std`) Several default logger implementations.
//!   - (With `stats_file_lock`) Safer file locking for `FileLog`. (MSRV ≥ 1.89.0).
//!   - (With `stats_parking_lot`) Usage of [`parking_lot::Mutex`] instead of [`std::sync::Mutex`].
//!
//! - **`external_alloc`**: FFI helpers for external allocators.
//!
//! - **`os_err_reporting`**: Enables OS error reporting on failed allocation for supported
//!   allocators.
//!   - Supported allocators: Jemalloc, Rust's default, `MiMalloc` if `mimalloc_err_reporting` is
//!     enabled.
//!
//! - **`jemalloc`**: Provides [`Jemalloc`], a ZST `Alloc` implementation using `Jemallocator`.
//!
//! - **`mimalloc`**: Provides [`MiMalloc`], a ZST `Alloc` implementation using `MiMalloc`.
//!   - **`mimalloc_err_reporting`**: Enables OS error reporting on failed allocation for
//!     `MiMalloc`.
//!   - **`mimalloc_error_output`**: Enables OS error reporting AND printing to stderr on failed
//!     allocation for `MiMalloc`.
//!
//! - **`nightly`**: Enables using the unstable `allocator_api`.
//!
//! - **`metadata`, `clone_to_uninit`, `specialization`, `sized_hierarchy`**: Enable using the
//!   nightly Rust feature of the same name.
//!
//! - **`extra_const`**: Enables additional `const` methods (MSRV ≥ 1.61.0).
//!
//! - **`c_str`**: Implements `UnsizedCopy` for `core::ffi::CStr` (MSRV ≥ 1.64.0).
//!
//! - **`extra_extra_const`**: Further expands `const` support (MSRV ≥ 1.83.0).
//!
//! All other features are either bundles of others or bindings to `MiMalloc`/`Jemalloc`'s features.

#![allow(unknown_lints)]
#![warn(clippy::all, clippy::pedantic, clippy::undocumented_unsafe_blocks)]
#![warn(unknown_lints)]
#![allow(
    unsafe_op_in_unsafe_fn,
    rustdoc::broken_intra_doc_links,
    // :) because patch doesn't work for overriding crates.io packages and i have to include my
    // dependencies' dependencies versions to make this compile on msrv
    unused_crate_dependencies
)]
#![deny(missing_docs, unused_unsafe)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "metadata", feature(ptr_metadata))]
#![cfg_attr(feature = "clone_to_uninit", feature(clone_to_uninit))]
#![cfg_attr(feature = "specialization", feature(min_specialization))]
#![cfg_attr(feature = "sized_hierarchy", feature(sized_hierarchy))]

// TODO: create fewer scopes (particularly with unsafe)

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
    // branch for a lifetime instead of type param
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
        pub const unsafe fn $name:ident $(<$generic_ty:ident $(: $req:ident)?>)? ( $($args:tt)* )
        $(-> $ret:ty)?
        $body:block
    ) => {
        #[cfg(feature = $feature)]
        #[doc = $docs]
        #[allow(clippy::incompatible_msrv)]
        $(#[$attr])*
        pub const unsafe fn $name$(<$generic_ty $(: $req)?>)?($($args)*) $(-> $ret)? $body

        #[cfg(not(feature = $feature))]
        #[doc = $docs]
        $(#[$attr])*
        pub unsafe fn $name$(<$generic_ty $(: $req)?>)?($($args)*) $(-> $ret)? $body
    };
}

/// This macro is theoretically faster than `<fallible>?`.
macro_rules! tri {
    ($($fallible:expr)+) => {
        match $($fallible)+ {
            Ok(s) => s,
            Err(e) => return Err(e),
        }
    };
    (il, $($fallible:expr)+) => {
        match $($fallible)+ {
            Ok(s) => s,
            Err(e) => return Err(AllocError::InvalidLayout(e)),
        }
    };
}

extern crate alloc;
extern crate core;

#[cfg(feature = "extern_alloc")]
pub(crate) mod external_alloc;

#[cfg(any(
    feature = "fallible_dealloc",
    feature = "alloc_ext",
    feature = "alloc_slice",
    feature = "resize_in_place",
    feature = "stats"
))]
mod features;

#[cfg(feature = "alloc_ext")]
pub use features::alloc_ext::*;
#[cfg(feature = "alloc_slice")]
pub use features::alloc_slice::*;
#[cfg(feature = "resize_in_place")]
pub use features::resize_in_place::*;

#[cfg(any(feature = "stats", feature = "fallible_dealloc"))]
pub use features::*;

#[cfg(feature = "extern_alloc")]
pub use external_alloc::*;

/// Marker traits.
pub mod marker;
/// Sized type properties as constants and property getters for pointers.
pub mod type_props;

/// Small alternatives to Rust functions that are unstable as of the most recent release.
pub mod unstable_util;

/// Errors that can occur during allocation.
pub mod error;

use alloc::alloc::{
    alloc as raw_all, alloc_zeroed as raw_allz, dealloc as de, realloc as re, GlobalAlloc, Layout,
};
use core::{
    cmp::Ordering,
    ptr::{self, NonNull},
};
use {error::AllocError, helpers::alloc_then};

/// Default allocator, delegating to the global allocator.
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefaultAlloc;

macro_rules! default_alloc_impl {
    ($ty:ty) => {
        impl Alloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
                $crate::helpers::null_q_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non zero-sized before use.
                    |layout| unsafe { raw_all(layout) },
                    $crate::helpers::null_q_dyn,
                )
            }

            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
                $crate::helpers::null_q_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non zero-sized before use.
                    |layout| unsafe { raw_allz(layout) },
                    $crate::helpers::null_q_dyn,
                )
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

// SAFETY: DefaultAlloc doesn't unwind, and all layout operations are correct
unsafe impl GlobalAlloc for DefaultAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        raw_all(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        de(ptr, layout);
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        raw_allz(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        re(ptr, layout, new_size)
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
        // SAFETY: alloc_zeroed returns at least layout.size() allocated bytes
        alloc_then(self, layout, (), |p, ()| unsafe {
            // SAFETY: alloc returns at least layout.size() allocated bytes
            ptr::write_bytes(p.as_ptr(), 0, layout.size());
            p
        })
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
    /// On failure, the original memory will not be deallocated or modified.
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
    /// On failure, the original memory will not be deallocated or modified.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[cfg_attr(miri, track_caller)]
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
    /// On failure, the original memory will not be deallocated or modified.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[cfg_attr(miri, track_caller)]
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
    /// On failure, the original memory will not be deallocated or modified.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[cfg_attr(miri, track_caller)]
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
    /// On failure, the original memory will not be deallocated or modified.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[cfg_attr(miri, track_caller)]
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
    use crate::{error::AllocError, Alloc, DefaultAlloc};
    use alloc::alloc::{
        alloc as raw_all, alloc_zeroed as raw_allz, dealloc as de, Allocator, Global, Layout,
    };
    use core::{alloc::AllocError as AllocatorError, ptr::NonNull};

    // SAFETY: DefaultAlloc's allocated memory isn't deallocated until a deallocation method is
    //  called. as a ZST allocator, copying/cloning it doesn't change behavior or invalidate
    //  allocations.
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

#[allow(clippy::inline_always)]
impl<A: Alloc + ?Sized> Alloc for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        (**self).alloc(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        (**self).alloc_zeroed(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        (**self).dealloc(ptr, layout);
    }
}

#[cfg(feature = "std")]
#[cfg_attr(miri, track_caller)]
fn zsl_check_alloc<A: GlobalAlloc>(
    a: &A,
    layout: Layout,
    alloc: unsafe fn(&A, Layout) -> *mut u8,
) -> Result<NonNull<u8>, AllocError> {
    helpers::zsl_check(layout, |layout: Layout| {
        // SAFETY: we check the layout is non-zero-sized before use.
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
/// This function doesn't check for layout validity.
/// Callers must ensure `new_layout.size()` is greater than `old_layout.size()`.
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(miri, track_caller)]
unsafe fn grow_unchecked<A: Alloc + ?Sized, F: Fn(usize) -> u8 + Clone>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError> {
    let new_ptr = match pattern {
        AllocPattern::None => tri!(a.alloc(new_layout)).cast::<u8>(),
        #[cfg(feature = "alloc_ext")]
        AllocPattern::Fn(f) => tri!(a.alloc_patterned(new_layout, f)),
        AllocPattern::Zero => tri!(a.alloc_zeroed(new_layout)).cast::<u8>(),
        #[cfg(feature = "alloc_ext")]
        AllocPattern::All(n) => tri!(a.alloc_filled(new_layout, n)).cast::<u8>(),
        #[cfg(not(feature = "alloc_ext"))]
        AllocPattern::PhantomFn(_) => core::hint::unreachable_unchecked(),
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
/// This function doesn't check for layout validity.
/// Callers must ensure `new_layout.size()` is greater than `old_layout.size()`.
#[cfg_attr(miri, track_caller)]
unsafe fn shrink_unchecked<A: Alloc + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> Result<NonNull<u8>, AllocError> {
    let new_ptr = tri!(a.alloc(new_layout)).cast::<u8>();

    ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_layout.size());
    a.dealloc(ptr, old_layout);

    Ok(new_ptr)
}

/// Helper for realloc to reduce repetition.
#[cfg_attr(miri, track_caller)]
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

/// Helpers that tend to be useful in other libraries as well.
pub mod helpers;
