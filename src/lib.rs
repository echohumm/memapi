//! A small, `no_std`/`no_alloc`-friendly memory allocation interface for managing raw buffers.
//!
//! This crate provides explicit layouts, a split allocator trait stack, and structured errors.
//! It is `no_std` by default but relies on the `alloc` crate unless `no_alloc` is enabled. Enable
//! `std` for system allocator integrations and `os_err_reporting` for richer diagnostics.
//!
//! # Core traits
//! - [`Alloc`], [`Dealloc`], [`Grow`], [`Shrink`], [`Realloc`]
//! - Convenience aliases: [`BasicAlloc`] and [`FullAlloc`]
//! - Mutable variants in [`alloc_mut`]: [`AllocMut`](alloc_mut::AllocMut),
//!   [`DeallocMut`](alloc_mut::DeallocMut), [`GrowMut`](alloc_mut::GrowMut),
//!   [`ShrinkMut`](alloc_mut::ShrinkMut), [`ReallocMut`](alloc_mut::ReallocMut),
//!   [`BasicAllocMut`](alloc_mut::BasicAllocMut), [`FullAllocMut`](alloc_mut::FullAllocMut)
//! - Optional scoped allocations (`alloc_temp_trait` feature): [`AllocTemp`](alloc_temp::AllocTemp)
//!
//! # Types and errors
//! - [`Layout`]: crate layout type (with conversion to/from [`StdLayout`] unless `no_alloc` feature
//!   is enabled)
//! - [`DefaultAlloc`]: default allocator wrapper that delegates to the global allocator
//! - Errors: [`Error`](error::Error), [`Cause`](error::Cause), [`LayoutErr`](error::LayoutErr),
//!   [`ArithErr`](error::ArithErr), [`ArithOp`](error::ArithOp)
//!
//! # Data and type utilities
//! - [`data::type_props`][]: [`SizedProps`](data::type_props::SizedProps),
//!   [`PtrProps`](data::type_props::PtrProps), [`VarSized`](data::type_props::VarSized),
//!   [`VarSizedStruct`](data::type_props::VarSizedStruct)
//! - [`data::marker`]: [`UnsizedCopy`](data::marker::UnsizedCopy), [`Thin`](data::marker::Thin),
//!   [`SizeMeta`](data::marker::SizeMeta)
//! - [`helpers`]: alignment, checked arithmetic, and pointer helpers
//!
//! # Allocator implementations
//! - [`DefaultAlloc`] (available unless `no_alloc` is enabled)
//! - [`std::alloc::System`](::std::alloc::System) when the `std` feature is enabled
//! - [`c_alloc::CAlloc`] behind the `c_alloc` feature
//! - [`stack_alloc::StackAlloc`] behind the `stack_alloc` feature
//!
//! # Feature flags
//! - `std`: enables `std` integration (including [`std::alloc::System`](::std::alloc::System))
//! - `os_err_reporting`: best-effort OS error reporting via `errno` (requires `std`)
//! - `alloc_temp_trait`: scoped/temporary allocation trait
//! - `c_alloc`: C `aligned_alloc`-style allocator ([`c_alloc`])
//! - `stack_alloc`: `alloca`-based allocator ([`stack_alloc`])
//! - `c_str`: enables `CStr`-specific data traits in `no_std` (MSRV: 1.64)
//! - `metadata`: enables [`core::ptr::Pointee`] metadata support on nightly
//! - `sized_hierarchy`: enables [`core::marker::MetaSized`] support on nightly
//! - `full`, `full_nightly`: convenience bundles for docs/tests

#![allow(unknown_lints)]
#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::multiple_unsafe_ops_per_block)]
#![allow(
    clippy::inline_always,
    clippy::borrow_as_ptr,
    clippy::module_name_repetitions,
    clippy::use_self,
    clippy::question_mark,
    unused_unsafe
)]
#![deny(missing_docs, unused_variables, clippy::undocumented_unsafe_blocks)]
#![warn(unknown_lints)]
#![no_implicit_prelude]
#![cfg_attr(feature = "dev", warn(rustdoc::broken_intra_doc_links))]
#![cfg_attr(not(feature = "std"), no_std)]
// nightly is set by the build.rs
#![cfg_attr(nightly, feature(allocator_api))]
#![cfg_attr(feature = "metadata", feature(ptr_metadata))]
#![cfg_attr(feature = "sized_hierarchy", feature(sized_hierarchy))]

// TODO: add any missing cfg_attr(miri, track_caller) attributes, remove unnecessary ones
// TODO: consider behavior of all allocation methods in all possible cases for all allocators and
//  make sure they match and make sense

// TODO: ideally `no_alloc` is ignored/switches to `std` if it's enabled

#[cfg(not(feature = "no_alloc"))] extern crate alloc as stdalloc;
extern crate core;
extern crate rustversion;

use ::core::result::{
    Result,
    Result::{Err, Ok}
};

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
    (cmap($err:expr) from $e:ty, $($fallible:expr)+) => {
        match $($fallible)+ {
            Ok(s) => s,
            Err(_) => return Err(<$e>::from($err)),
        }
    };
}

macro_rules! zalloc {
    ($self:ident, $alloc:ident, $layout:ident) => {{
        let res = $self.$alloc($layout);
        if let Ok(p) = res {
            // SAFETY: alloc returns at least layout.size() allocated bytes
            unsafe {
                ptr::write_bytes(p.as_ptr(), 0, $layout.size());
            }
        }
        res
    }};
}

macro_rules! default_dealloc {
    ($self:ident.$de:ident, $ptr:ident, $l:ident) => {
        if $l.is_nonzero_sized() && $ptr != $l.dangling() {
            if let Err(e) = $self.$de($ptr, $l) {
                default_dealloc_panic($ptr, $l, e)
            }
        }
    };
}

macro_rules! default_shrink {
    ($self:ident::$unchecked:ident, $ptr:ident, $old:ident, $new:ident) => {
        match $old.size().cmp(&$new.size()) {
            Ordering::Less => Err(<Self as AllocError>::Error::from(Error::ShrinkLargerNewLayout(
                $old.size(),
                $new.size()
            ))),
            Ordering::Equal => {
                if $new.align() > $old.align() {
                    $unchecked($self, $ptr, $old, $new)
                } else {
                    Ok($ptr)
                }
            }
            Ordering::Greater => $unchecked($self, $ptr, $old, $new)
        }
    };
}

/// All traits provided by this crate.
pub mod traits;
pub use traits::*;

/// Helpers that tend to be useful in other libraries as well.
pub mod helpers;

/// Errors that can occur during allocation.
pub mod error;

mod layout;
pub use layout::Layout;

mod ffi;

mod allocs;
#[allow(unused_imports)] pub use allocs::*;

#[cfg(not(feature = "no_alloc"))]
/// A type alias for [`alloc::alloc::Layout`](::stdalloc::alloc::Layout).
pub type StdLayout = ::stdalloc::alloc::Layout;

/// Default allocator, delegating to the global allocator.
///
/// # Note
///
/// This must _not_ be set as the global allocator (via `#[global_allocator]`). Doing so will lead
/// to infinite recursion, as the allocation functions this calls (in
/// [`alloc::alloc`](::stdalloc::alloc)) delegate to the global allocator.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefaultAlloc;

macro_rules! default_alloc_impl {
    ($ty:ty) => {
        #[cfg(not(feature = "no_alloc"))]
        impl crate::AllocError for $ty {
            type Error = crate::error::Error;
        }

        #[cfg(not(feature = "no_alloc"))]
        impl crate::Alloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn alloc(
                &self,
                layout: Layout
            ) -> Result<::core::ptr::NonNull<u8>, crate::error::Error> {
                crate::helpers::null_q_dyn_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non-zero-sized before use.
                    |layout| unsafe { ::stdalloc::alloc::alloc(layout.to_stdlib()) }
                )
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn zalloc(
                &self,
                layout: Layout
            ) -> Result<::core::ptr::NonNull<u8>, crate::error::Error> {
                crate::helpers::null_q_dyn_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non-zero-sized before use.
                    |layout| unsafe { ::stdalloc::alloc::alloc_zeroed(layout.to_stdlib()) }
                )
            }
        }
        #[cfg(not(feature = "no_alloc"))]
        impl crate::Dealloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn dealloc(&self, ptr: ::core::ptr::NonNull<u8>, layout: Layout) {
                if layout.is_nonzero_sized() && ptr != layout.dangling() {
                    ::stdalloc::alloc::dealloc(ptr.as_ptr(), layout.to_stdlib());
                }
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn try_dealloc(
                &self,
                ptr: ::core::ptr::NonNull<u8>,
                layout: Layout
            ) -> Result<(), crate::error::Error> {
                if layout.is_zero_sized() {
                    Err(crate::error::Error::ZeroSizedLayout)
                } else if ptr == layout.dangling() {
                    Err(crate::error::Error::DanglingDeallocation)
                } else {
                    ::stdalloc::alloc::dealloc(ptr.as_ptr(), layout.to_stdlib());
                    Ok(())
                }
            }
        }
        #[cfg(not(feature = "no_alloc"))]
        impl crate::Grow for $ty {}
        #[cfg(not(feature = "no_alloc"))]
        impl crate::Shrink for $ty {}
        #[cfg(not(feature = "no_alloc"))]
        impl crate::Realloc for $ty {}
    };
}

#[cfg(not(feature = "no_alloc"))]
// SAFETY: DefaultAlloc doesn't unwind, and all layout operations are correct
unsafe impl ::stdalloc::alloc::GlobalAlloc for DefaultAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc(&self, layout: StdLayout) -> *mut u8 {
        ::stdalloc::alloc::alloc(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: StdLayout) {
        ::stdalloc::alloc::dealloc(ptr, layout);
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: StdLayout) -> *mut u8 {
        ::stdalloc::alloc::alloc_zeroed(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: StdLayout, new_size: usize) -> *mut u8 {
        ::stdalloc::alloc::realloc(ptr, layout, new_size)
    }
}

default_alloc_impl!(DefaultAlloc);

#[cfg(all(nightly, not(feature = "no_alloc")))]
/// The primary module for when `nightly` is enabled.
pub(crate) mod nightly {
    use {
        crate::{Layout, StdLayout},
        ::core::{
            ptr::NonNull,
            result::Result::{self, Err, Ok}
        },
        ::stdalloc::alloc::{AllocError, Allocator, Global}
    };

    // SAFETY: DefaultAlloc's allocated memory isn't deallocated until a deallocation method is
    //  called. as a ZST allocator, copying/cloning it doesn't change behaviour or invalidate
    //  allocations.
    unsafe impl Allocator for crate::DefaultAlloc {
        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate(&self, layout: StdLayout) -> Result<NonNull<[u8]>, AllocError> {
            Allocator::allocate(&Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate_zeroed(&self, layout: StdLayout) -> Result<NonNull<[u8]>, AllocError> {
            Allocator::allocate_zeroed(&Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: StdLayout) {
            Allocator::deallocate(&Global, ptr.cast(), layout);
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow(
            &self,
            ptr: NonNull<u8>,
            old_layout: StdLayout,
            new: StdLayout
        ) -> Result<NonNull<[u8]>, AllocError> {
            Allocator::grow(&Global, ptr.cast(), old_layout, new)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow_zeroed(
            &self,
            ptr: NonNull<u8>,
            old_layout: StdLayout,
            new: StdLayout
        ) -> Result<NonNull<[u8]>, AllocError> {
            Allocator::grow_zeroed(&Global, ptr.cast(), old_layout, new)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn shrink(
            &self,
            ptr: NonNull<u8>,
            old_layout: StdLayout,
            new: StdLayout
        ) -> Result<NonNull<[u8]>, AllocError> {
            Allocator::shrink(&Global, ptr.cast(), old_layout, new)
        }
    }

    default_alloc_impl!(Global);

    // TODO: either Allocator for A: Alloc or vice versa, not sure which. i think i removed that at
    // some point but i can't remember why.
}
