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

// TODO: add more tests and benches
// TODO: test on other platforms/targets

#![allow(unknown_lints)]
#![warn(
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    // TEMPORARY
    // clippy::undocumented_unsafe_blocks,
    // clippy::multiple_unsafe_ops_per_block,
    // clippy::missing_docs_in_private_items,
)]
#![allow(clippy::borrow_as_ptr)]
#![warn(unknown_lints)]
#![allow(
    rustdoc::broken_intra_doc_links,
    // does anyone else hate the Self keyword? that capital letter there looks so ugly idk why
    clippy::use_self,
    unused_unsafe
)]
#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "metadata", feature(ptr_metadata))]
#![cfg_attr(feature = "sized_hierarchy", feature(sized_hierarchy))]

// TODO: add any missing cfg_attr(miri, track_caller) attributes, remove unnecessary ones
// TODO: a lot of helpers and unstable utils would be good to have in another crate, maybe?

extern crate alloc;
extern crate core;
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
        #[allow(unknown_lints, clippy::missing_const_for_fn)]
        pub fn $name $(<$generic_ty $(: $req)?>)? ($($args)*)
        $(-> $ret)? $(where $where_ty: $where_req)? $body
    };

    (
        $feature:literal,
        $docs:literal,
        $(#[$attr:meta])*
        // this is also pretty poorly done, but it makes type param and optional req work
        const unsafe fn $name:ident $(<$generic_ty:ident $(: ?$req:ident)? $(+ $req2:ident)?>)? ( $($args:tt)* )
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
        const unsafe fn $name $(<$generic_ty $(: ?$req)? $(+ $req2)?>)? ($($args)*)
        $(-> $ret)? $(where $where_ty: $where_req)? $body

        // when the feature is disabled, drop the `const`
        #[cfg(not(feature = $feature))]
        #[doc = $docs]
        $(#[$attr])*
        #[allow(unknown_lints, clippy::missing_const_for_fn)]
        unsafe fn $name $(<$generic_ty $(: ?$req)? $(+ $req2)?>)? ($($args)*)
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
    // branch for relaxed bound + second bound
    (
        $feature:literal,
        $docs:literal,
        $(#[$attr:meta])*
        pub const fn $name:ident <$generic_ty:ident: ?Sized + $req:ident> ($($args:tt)*)
        $(-> $ret:ty)?
        $body:block
    ) => {
        #[cfg(feature = $feature)]
        #[doc = $docs]
        #[allow(clippy::incompatible_msrv)]
        $(#[$attr])*
        pub const fn $name <$generic_ty: ?Sized + $req> ($($args)*)
        $(-> $ret)? $body

        #[cfg(not(feature = $feature))]
        #[doc = $docs]
        $(#[$attr])*
        pub fn $name <$generic_ty: ?Sized + $req> ($($args)*)
        $(-> $ret)? $body
    }
}

/// This macro is theoretically faster than `<fallible>?`.
macro_rules! tri {
    (do $($fallible:expr)+) => {
        match $($fallible)+ {
            Ok(s) => s,
            Err(e) => return Err(e),
        }
    };
}

// TODO: split crate into smaller crates (memapi-jemalloc, memapi-mimalloc, etc.)
//  (removed stuff is stuff which would go in new crate)

/// Module for anything related specifically to data.
///
/// This includes marker traits, type properties, and miscellaneous data-handling traits.
pub mod data;

/// The library's main traits.
pub mod traits;
pub use traits::*;

/// Errors that can occur during allocation.
pub mod error;

use core::alloc::Layout;

/// Default allocator, delegating to the global allocator.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefaultAlloc;

#[allow(unused_macros)]
macro_rules! default_alloc_impl {
    ($ty:ty) => {
        impl crate::Alloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn alloc(
                &self,
                layout: Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::helpers::null_q_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non-zero-sized before use.
                    |layout| unsafe { alloc::alloc::alloc(layout) },
                    crate::helpers::null_q_dyn
                )
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn zalloc(
                &self,
                layout: Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::helpers::null_q_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non-zero-sized before use.
                    |layout| unsafe { alloc::alloc::alloc_zeroed(layout) },
                    crate::helpers::null_q_dyn
                )
            }
        }
        impl crate::Dealloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn dealloc(&self, ptr: core::ptr::NonNull<u8>, layout: Layout) {
                if layout.size() != 0 {
                    alloc::alloc::dealloc(ptr.as_ptr(), layout);
                }
            }
        }
        // TODO: manual impls should be faster, but may not be worth it with the duplicated code
        impl crate::Grow for $ty {}
        impl crate::Shrink for $ty {}
        impl crate::Realloc for $ty {}
    };
}

// SAFETY: DefaultAlloc doesn't unwind, and all layout operations are correct
unsafe impl alloc::alloc::GlobalAlloc for DefaultAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        alloc::alloc::alloc(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        alloc::alloc::dealloc(ptr, layout);
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        alloc::alloc::alloc_zeroed(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        alloc::alloc::realloc(ptr, layout, new_size)
    }
}

default_alloc_impl!(DefaultAlloc);

#[cfg(feature = "nightly")]
/// The primary module for when `nightly` is enabled.
pub(crate) mod nightly {
    use core::alloc::Layout;
    // SAFETY: DefaultAlloc's allocated memory isn't deallocated until a deallocation method is
    //  called. as a ZST allocator, copying/cloning it doesn't change behavior or invalidate
    //  allocations.
    unsafe impl alloc::alloc::Allocator for crate::DefaultAlloc {
        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate(
            &self,
            layout: Layout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::allocate(&alloc::alloc::Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate_zeroed(
            &self,
            layout: Layout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::allocate_zeroed(&alloc::alloc::Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn deallocate(&self, ptr: core::ptr::NonNull<u8>, layout: Layout) {
            alloc::alloc::Allocator::deallocate(&alloc::alloc::Global, ptr.cast(), layout);
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow(
            &self,
            ptr: core::ptr::NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::grow(&alloc::alloc::Global, ptr.cast(), old_layout, new_layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow_zeroed(
            &self,
            ptr: core::ptr::NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout
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
            old_layout: Layout,
            new_layout: Layout
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
