//! A small, `no_std`-friendly memory allocation interface for managing raw
//! buffers, suitable for use in collections.
//!
//! This crate focuses on a minimal API:
//! - [`Alloc`]: a trait defining basic allocation, zero-allocation, deallocation, and simple
//!   grow/shrink helpers.
//! - [`DefaultAlloc`]: a tiny wrapper delegating to the global allocator.
//! - [`AllocError`]: an error type describing allocation failures.
//!
//! Some utilities and marker traits are provided under [`data`]:
//! - [`PtrProps`](data::type_props::PtrProps)
//! - [`SizedProps`](data::type_props::SizedProps)
//! - [`VarSized`](data::type_props::VarSized)
//! - [`UnsizedCopy`](data::marker::UnsizedCopy)
//! - [`Thin`](data::marker::Thin)

// TODO: add more tests. ALWAYS MORE TESTS.
//  for error cases specifically

#![allow(unknown_lints)]
#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::multiple_unsafe_ops_per_block)]
#![allow(clippy::borrow_as_ptr)]
#![warn(unknown_lints)]
#![cfg_attr(feature = "dev", warn(rustdoc::broken_intra_doc_links))]
#![allow(
    // does anyone else hate the Self keyword? that capital letter there looks so ugly idk why
    clippy::use_self,
    unused_unsafe
)]
#![deny(missing_docs, clippy::undocumented_unsafe_blocks)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "metadata", feature(ptr_metadata))]
#![cfg_attr(feature = "sized_hierarchy", feature(sized_hierarchy))]

// TODO: add any missing cfg_attr(miri, track_caller) attributes, remove unnecessary ones
// TODO: consider behavior of all allocation methods in all possible cases for all allocators and
//  make sure they match and make sense

// TODO: split crate into smaller crates (memapi-jemalloc, memapi-mimalloc, etc.)
//  (removed stuff is stuff which would go in new crates)
//  a lot of helpers would be good to have in another crate too, like .*AllocGuard, checked_op, etc.

extern crate alloc;
extern crate core;

/// This macro is theoretically faster than `<fallible>?`.
macro_rules! tri {
    (::$err:ident $($fallible:expr)+) => {
        match $($fallible)+ {
            Ok(x) => x,
            Err(e) => return Err(Error::$err(e)),
        }
    };
    (opt $($fallible:expr)+) => {
        match $($fallible)+ {
            Some(x) => x,
            None => return None,
        }
    };
    (do $($fallible:expr)+) => {
        match $($fallible)+ {
            Ok(s) => s,
            Err(e) => return Err(e),
        }
    };
}

#[cfg(feature = "c_alloc")]
/// An allocator which uses C's [`aligned_alloc`](c_alloc::ffi::c_alloc) set of allocation
/// functions.
pub mod c_alloc;
/// Module for anything related specifically to data.
///
/// This includes marker traits, type properties, and miscellaneous data-handling traits.
pub mod data;

/// The library's main traits.
pub mod traits;
pub use traits::*;

/// Errors that can occur during allocation.
pub mod error;
mod layout;

pub use layout::Layout;

/// A type alias for [`alloc::alloc::Layout`].
pub type StdLayout = alloc::alloc::Layout;

/// Default allocator, delegating to the global allocator.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefaultAlloc;

#[allow(unused_macros)]
macro_rules! default_alloc_impl {
    ($ty:ty) => {
        impl crate::Alloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn alloc(&self, layout: Layout) -> Result<core::ptr::NonNull<u8>, crate::error::Error> {
                crate::helpers::null_q_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non-zero-sized before use.
                    |layout| unsafe { alloc::alloc::alloc(layout.to_stdlib()) },
                    crate::helpers::null_q_dyn
                )
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn zalloc(
                &self,
                layout: Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::Error> {
                crate::helpers::null_q_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non-zero-sized before use.
                    |layout| unsafe { alloc::alloc::alloc_zeroed(layout.to_stdlib()) },
                    crate::helpers::null_q_dyn
                )
            }
        }
        impl crate::Dealloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn dealloc(&self, ptr: core::ptr::NonNull<u8>, layout: Layout) {
                if layout.size() != 0 {
                    alloc::alloc::dealloc(ptr.as_ptr(), layout.to_stdlib());
                }
            }
        }
        impl crate::Grow for $ty {}
        impl crate::Shrink for $ty {}
        impl crate::Realloc for $ty {}
    };
}

// SAFETY: DefaultAlloc doesn't unwind, and all layout operations are correct
unsafe impl alloc::alloc::GlobalAlloc for DefaultAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc(&self, layout: StdLayout) -> *mut u8 {
        alloc::alloc::alloc(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: StdLayout) {
        alloc::alloc::dealloc(ptr, layout);
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: StdLayout) -> *mut u8 {
        alloc::alloc::alloc_zeroed(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: StdLayout, new_size: usize) -> *mut u8 {
        alloc::alloc::realloc(ptr, layout, new_size)
    }
}

default_alloc_impl!(DefaultAlloc);

#[cfg(feature = "nightly")]
/// The primary module for when `nightly` is enabled.
pub(crate) mod nightly {
    use crate::{Layout, StdLayout};

    // SAFETY: DefaultAlloc's allocated memory isn't deallocated until a deallocation method is
    //  called. as a ZST allocator, copying/cloning it doesn't change behavior or invalidate
    //  allocations.
    unsafe impl alloc::alloc::Allocator for crate::DefaultAlloc {
        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate(
            &self,
            layout: StdLayout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::allocate(&alloc::alloc::Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate_zeroed(
            &self,
            layout: StdLayout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::allocate_zeroed(&alloc::alloc::Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn deallocate(&self, ptr: core::ptr::NonNull<u8>, layout: StdLayout) {
            alloc::alloc::Allocator::deallocate(&alloc::alloc::Global, ptr.cast(), layout);
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow(
            &self,
            ptr: core::ptr::NonNull<u8>,
            old_layout: StdLayout,
            new_layout: StdLayout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::grow(&alloc::alloc::Global, ptr.cast(), old_layout, new_layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow_zeroed(
            &self,
            ptr: core::ptr::NonNull<u8>,
            old_layout: StdLayout,
            new_layout: StdLayout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::grow_zeroed(
                &alloc::alloc::Global,
                ptr.cast(),
                old_layout,
                new_layout
            )
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn shrink(
            &self,
            ptr: core::ptr::NonNull<u8>,
            old_layout: StdLayout,
            new_layout: StdLayout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::shrink(
                &alloc::alloc::Global,
                ptr.cast(),
                old_layout,
                new_layout
            )
        }
    }

    default_alloc_impl!(alloc::alloc::Global);
}

/// Helpers that tend to be useful in other libraries as well.
pub mod helpers;
