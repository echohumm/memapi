//! A small, `no_std`/`no_alloc`-friendly memory allocation interface for managing raw buffers.
//!
//! This crate provides explicit layouts, a split allocator trait stack, and structured errors.
//! It is `no_std` by default but relies on the `alloc` crate unless `no_alloc` is enabled. Enable
//! `std` for system allocator integrations and `os_err_reporting` for richer diagnostics.
//!
//! # Core traits
//! - [`Alloc`], [`Dealloc`], [`Grow`], [`Shrink`], [`Realloc`]
//! - Convenience aliases: [`BasicAlloc`] and [`FullAlloc`]
//! - Optional mutable variants (`alloc_mut_traits`): [`AllocMut`], [`DeallocMut`], [`GrowMut`],
//!   [`ShrinkMut`], [`ReallocMut`], [`BasicAllocMut`], [`FullAllocMut`]
//! - Optional scoped allocations (`alloc_temp_trait`): [`AllocTemp`]
//!
//! # Types and errors
//! - [`Layout`]: crate layout type (with conversion to/from [`StdLayout`] unless `no_alloc` is
//!   enabled)
//! - [`DefaultAlloc`]: default allocator wrapper that delegates to the global allocator
//! - Errors: [`Error`], [`Cause`], [`LayoutErr`], [`ArithErr`], [`ArithOp`]
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
//! - [`std::alloc::System`] when the `std` feature is enabled
//! - [`c_alloc::CAlloc`] behind the `c_alloc` feature
//! - [`stack_alloc::StackAlloc`] behind the `stack_alloc` feature
//!
//! # Feature flags
//! - `std`: enables `std` integration (including [`std::alloc::System`])
//! - `os_err_reporting`: best-effort OS error reporting via `errno` (requires `std`)
//! - `alloc_mut_traits`: mutable allocator trait variants
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
#![deny(missing_docs, clippy::undocumented_unsafe_blocks)]
#![warn(unknown_lints)]
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

#[cfg(not(feature = "no_alloc"))] extern crate alloc;
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

/// The library's main traits.
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
/// A type alias for [`alloc::alloc::Layout`].
pub type StdLayout = alloc::alloc::Layout;

/// Default allocator, delegating to the global allocator.
///
/// # Note
///
/// This must _not_ be set as the global allocator (via `#[global_allocator]`). Doing so will lead
/// to infinite recursion, as the allocation functions this calls (in [`alloc::alloc`]) delegate to
/// the global allocator.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefaultAlloc;

macro_rules! default_alloc_impl {
    ($ty:ty) => {
        #[cfg(not(feature = "no_alloc"))]
        impl crate::Alloc for $ty {
            type Error = crate::error::Error;

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn alloc(&self, layout: Layout) -> Result<core::ptr::NonNull<u8>, crate::error::Error> {
                crate::helpers::null_q_dyn_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non-zero-sized before use.
                    |layout| unsafe { alloc::alloc::alloc(layout.to_stdlib()) }
                )
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn zalloc(
                &self,
                layout: Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::Error> {
                crate::helpers::null_q_dyn_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non-zero-sized before use.
                    |layout| unsafe { alloc::alloc::alloc_zeroed(layout.to_stdlib()) }
                )
            }
        }
        #[cfg(not(feature = "no_alloc"))]
        impl crate::Dealloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn dealloc(&self, ptr: core::ptr::NonNull<u8>, layout: Layout) {
                if layout.is_nonzero_sized() {
                    alloc::alloc::dealloc(ptr.as_ptr(), layout.to_stdlib());
                }
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn try_dealloc(
                &self,
                ptr: core::ptr::NonNull<u8>,
                layout: Layout
            ) -> Result<(), crate::error::Error> {
                self.dealloc(ptr, layout);
                Ok(())
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

#[cfg(all(nightly, not(feature = "no_alloc")))]
/// The primary module for when `nightly` is enabled.
pub(crate) mod nightly {
    use {
        crate::{Layout, StdLayout},
        alloc::alloc::{AllocError, Allocator, Global},
        core::ptr::NonNull
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
            new_layout: StdLayout
        ) -> Result<NonNull<[u8]>, AllocError> {
            Allocator::grow(&Global, ptr.cast(), old_layout, new_layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow_zeroed(
            &self,
            ptr: NonNull<u8>,
            old_layout: StdLayout,
            new_layout: StdLayout
        ) -> Result<NonNull<[u8]>, AllocError> {
            Allocator::grow_zeroed(&Global, ptr.cast(), old_layout, new_layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn shrink(
            &self,
            ptr: NonNull<u8>,
            old_layout: StdLayout,
            new_layout: StdLayout
        ) -> Result<NonNull<[u8]>, AllocError> {
            Allocator::shrink(&Global, ptr.cast(), old_layout, new_layout)
        }
    }

    default_alloc_impl!(Global);

    // TODO: either Allocator for A: Alloc or vice versa, not sure which. i think i removed that at
    // some point but i can't remember why.
}
