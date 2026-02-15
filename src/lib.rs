//! A small, `no_std`/`no_alloc`-friendly memory allocation interface for managing raw buffers.
//!
//! This crate provides explicit layouts, a split allocator trait stack, and structured errors.
//! It is `no_std` by default but relies on the `alloc` crate unless `no_alloc` is enabled. Enable
//! `std` for system allocator integrations and `os_err_reporting` for richer diagnostics.
//!
//! # Core traits
//! - [`Alloc`](traits::alloc::Alloc), [`Dealloc`](traits::alloc::Dealloc),
//!   [`Grow`](traits::alloc::Grow), [`Shrink`](traits::alloc::Shrink),
//!   [`Realloc`](traits::alloc::Realloc)
//! - Convenience aliases: [`BasicAlloc`](traits::alloc::BasicAlloc) and
//!   [`FullAlloc`](traits::alloc::FullAlloc)
//! - Mutable variants in [`alloc_mut`](traits::alloc_mut):
//!   [`AllocMut`](traits::alloc_mut::AllocMut), [`DeallocMut`](traits::alloc_mut::DeallocMut),
//!   [`GrowMut`](traits::alloc_mut::GrowMut), [`ShrinkMut`](traits::alloc_mut::ShrinkMut),
//!   [`ReallocMut`](traits::alloc_mut::ReallocMut),
//!   [`BasicAllocMut`](traits::alloc_mut::BasicAllocMut),
//!   [`FullAllocMut`](traits::alloc_mut::FullAllocMut)
//! - Optional scoped allocations (`alloc_temp_trait` feature):
//!   [`AllocTemp`](traits::alloc_temp::AllocTemp)
//!
//! # Types and errors
//! - [`Layout`](layout::Layout): crate layout type (with conversion to/from
//!   [`StdLayout`](layout::StdLayout) unless `no_alloc` is enabled and `std` isn't)
//! - [`DefaultAlloc`]: default allocator wrapper that delegates to the global allocator
//! - Errors: [`Error`](error::Error), [`Cause`](error::Cause), [`LayoutErr`](error::LayoutErr),
//!   [`ArithErr`](error::ArithErr), [`ArithOp`](error::ArithOp)
//!
//! # Data and type utilities
//! - [`traits::data::type_props`][]: [`SizedProps`](traits::data::type_props::SizedProps),
//!   [`PtrProps`](traits::data::type_props::PtrProps),
//!   [`VarSized`](traits::data::type_props::VarSized),
//!   [`VarSizedStruct`](traits::data::type_props::VarSizedStruct)
//! - [`traits::data::marker`][]: [`UnsizedCopy`](traits::data::marker::UnsizedCopy),
//!   [`Thin`](traits::data::marker::Thin), [`SizeMeta`](traits::data::marker::SizeMeta)
//! - [`helpers`]: alignment, checked arithmetic, and pointer helpers
//!
//! # Allocator implementations
//! - [`DefaultAlloc`] (available unless `no_alloc` is enabled and `std` isn't)
//! - [`System`](::std::alloc::System) when the `std` feature is enabled
//! - [`CAlloc`](allocs::c_alloc::CAlloc) behind the `c_alloc` feature
//! - [`StackAlloc`](allocs::stack_alloc::StackAlloc) behind the `stack_alloc` feature
//!
//! # Feature flags
//! - `no_alloc` disables usage of the rust `alloc` crate; `std` crate is used instead if the `std`
//!   feature is enabled.
//! - `std`: enables `std` integration (including [`System`](::std::alloc::System))
//! - `os_err_reporting`: best-effort OS error reporting via `errno` (requires `std`)
//! - `alloc_temp_trait`: scoped/temporary allocation trait
//! - `c_alloc`: C `posix_memalign`-style allocator ([`allocs::c_alloc`])
//! - `stack_alloc`: `alloca`-based allocator ([`allocs::stack_alloc`])
//! - `c_str`: enables `CStr`-specific data traits in `no_std` (MSRV: 1.64)
//! - `metadata`: enables [`core::ptr::Pointee`] metadata support on nightly
//! - `sized_hierarchy`: enables [`core::marker::MetaSized`] support on nightly
//! - `full`, `full_nightly`: convenience bundles

#![allow(unknown_lints)]
#![deny(
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::multiple_unsafe_ops_per_block,
    clippy::undocumented_unsafe_blocks,
    missing_docs
)]
#![warn(clippy::missing_errors_doc)]
#![allow(
    clippy::inline_always,
    clippy::borrow_as_ptr,
    clippy::module_name_repetitions,
    clippy::use_self,
    clippy::question_mark,
    unused_unsafe
)]
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

extern crate core;
extern crate rustversion;
#[cfg(feature = "c_alloc")]
extern crate cty;

#[cfg(not(feature = "no_alloc"))] extern crate alloc as stdalloc;
#[cfg(all(feature = "std", feature = "no_alloc"))] extern crate std as stdalloc;

/// A relatively minimal prelude containing the most common, important things from this crate.
// unfortunately we need this cfg_attr, or it thinks rustfmt is a module and can't find it
#[allow(clippy::deprecated_cfg_attr)]
#[cfg_attr(rustfmt, rustfmt::skip)]
pub mod prelude {
    pub use crate::{
        // default allocator and layout are necessary
        DefaultAlloc,
        error::Error,
        layout::Layout,
        // traits are useful as well
        traits::{
            AllocError,
            alloc::{Alloc, BasicAlloc, Dealloc, FullAlloc, Grow, Realloc, Shrink},
            alloc_mut::{
                AllocMut,
                BasicAllocMut,
                DeallocMut,
                FullAllocMut,
                GrowMut,
                ReallocMut,
                ShrinkMut
            },
            data::type_props::{PtrProps, SizedProps},
            data::marker::{SizeMeta, Thin, UnsizedCopy}
        }
    };
    
    // alloc_temp trait too if the feature is on
    #[cfg(feature = "alloc_temp_trait")] pub use crate::traits::alloc_temp::AllocTemp;

    // and extra allocators that are enabled
    #[cfg(feature = "c_alloc")] pub use crate::allocs::c_alloc::CAlloc;
    #[cfg(feature = "stack_alloc")] pub use crate::allocs::stack_alloc::StackAlloc;
}

/// This macro is theoretically faster than `<fallible>?`.
macro_rules! tri {
    (::$err:ident $($fallible:expr)+) => {
        match $($fallible)+ {
            ::core::result::Result::Ok(x) => x,
            ::core::result::Result::Err(e) => return ::core::result::Result::Err(Error::$err(e)),
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
            ::core::result::Result::Ok(s) => s,
            ::core::result::Result::Err(e) => return ::core::result::Result::Err(e),
        }
    };
    (cmap($err:expr) from $e:ty, $($fallible:expr)+) => {
        match $($fallible)+ {
            ::core::result::Result::Ok(s) => s,
            ::core::result::Result::Err(_) => return ::core::result::Result::Err(<$e>::from($err)),
        }
    };
}

macro_rules! zalloc {
    ($self:ident, $alloc:ident, $layout:ident) => {{
        let res = $self.$alloc($layout);
        if let ::core::result::Result::Ok(p) = res {
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
            if let ::core::result::Result::Err(e) = $self.$de($ptr, $l) {
                default_dealloc_panic($ptr, $l, e)
            }
        }
    };
}

macro_rules! default_shrink {
    ($self:ident::$unchecked:ident, $ptr:ident, $old:ident, $new:ident) => {
        match $new.size().cmp(&$old.size()) {
            Ordering::Greater => ::core::result::Result::Err(<Self as AllocError>::Error::from(
                Error::ShrinkLargerNewLayout($old.size(), $new.size())
            )),
            Ordering::Equal => {
                if $new.align() > $old.align() {
                    $unchecked($self, $ptr, $old, $new)
                } else {
                    ::core::result::Result::Ok($ptr)
                }
            }
            Ordering::Less => $unchecked($self, $ptr, $old, $new)
        }
    };
}

/// All traits provided by this crate.
pub mod traits;

/// Helpers that tend to be useful in other libraries as well.
pub mod helpers;

/// Errors that can occur during allocation.
pub mod error;

/// A custom layout type to get around some strange Rust stdlib limitations.
pub mod layout;

#[cfg(any(feature = "c_alloc", feature = "stack_alloc"))]
/// Additional allocators which this crate supports.
pub mod allocs;

#[cfg(any(feature = "c_alloc", feature = "stack_alloc"))]
/// FFI backing any extra enabled allocators.
pub mod ffi;

/// Default allocator, delegating to the global allocator.
///
/// # Note
///
/// This must _not_ be set as the global allocator (via `#[global_allocator]`). Doing so will lead
/// to infinite recursion, as the allocation functions this calls (in
/// [`alloc::alloc`](::stdalloc::alloc)) delegate to the global allocator.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefaultAlloc;

#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
macro_rules! default_alloc_impl {
    ($ty:ty) => {
        impl crate::traits::AllocError for $ty {
            type Error = crate::error::Error;
        }

        impl crate::traits::alloc::Alloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn alloc(
                &self,
                layout: crate::layout::Layout
            ) -> ::core::result::Result<::core::ptr::NonNull<u8>, crate::error::Error> {
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
                layout: crate::layout::Layout
            ) -> ::core::result::Result<::core::ptr::NonNull<u8>, crate::error::Error> {
                crate::helpers::null_q_dyn_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non-zero-sized before use.
                    |layout| unsafe { ::stdalloc::alloc::alloc_zeroed(layout.to_stdlib()) }
                )
            }
        }
        impl crate::traits::alloc::Dealloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn dealloc(&self, ptr: ::core::ptr::NonNull<u8>, layout: crate::layout::Layout) {
                if layout.is_nonzero_sized() && ptr != layout.dangling() {
                    ::stdalloc::alloc::dealloc(ptr.as_ptr(), layout.to_stdlib());
                }
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn try_dealloc(
                &self,
                ptr: ::core::ptr::NonNull<u8>,
                layout: crate::layout::Layout
            ) -> ::core::result::Result<(), crate::error::Error> {
                if layout.is_zero_sized() {
                    ::core::result::Result::Err(crate::error::Error::ZeroSizedLayout)
                } else if ptr == layout.dangling() {
                    ::core::result::Result::Err(crate::error::Error::DanglingDeallocation)
                } else {
                    ::stdalloc::alloc::dealloc(ptr.as_ptr(), layout.to_stdlib());
                    ::core::result::Result::Ok(())
                }
            }
        }
        impl crate::traits::alloc::Grow for $ty {}
        impl crate::traits::alloc::Shrink for $ty {}
        impl crate::traits::alloc::Realloc for $ty {}
    };
}

#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
// SAFETY: DefaultAlloc doesn't unwind, and all layout operations are correct
unsafe impl ::stdalloc::alloc::GlobalAlloc for DefaultAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc(&self, layout: crate::layout::StdLayout) -> *mut u8 {
        ::stdalloc::alloc::alloc(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: crate::layout::StdLayout) {
        ::stdalloc::alloc::dealloc(ptr, layout);
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: crate::layout::StdLayout) -> *mut u8 {
        ::stdalloc::alloc::alloc_zeroed(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(
        &self,
        ptr: *mut u8,
        layout: crate::layout::StdLayout,
        new_size: usize
    ) -> *mut u8 {
        ::stdalloc::alloc::realloc(ptr, layout, new_size)
    }
}

#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
default_alloc_impl!(DefaultAlloc);

#[cfg(all(nightly, not(feature = "no_alloc")))]
/// The primary module for when `nightly` is enabled.
pub(crate) mod nightly {
    use {
        ::core::ptr::NonNull,
        ::stdalloc::alloc::{AllocError, Allocator, Global}
    };

    // SAFETY: DefaultAlloc's allocated memory isn't deallocated until a deallocation method is
    //  called. as a ZST allocator, copying/cloning it doesn't change behavior or invalidate
    //  allocations.
    unsafe impl Allocator for crate::DefaultAlloc {
        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate(
            &self,
            layout: crate::layout::StdLayout
        ) -> ::core::result::Result<NonNull<[u8]>, AllocError> {
            Allocator::allocate(&Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate_zeroed(
            &self,
            layout: crate::layout::StdLayout
        ) -> ::core::result::Result<NonNull<[u8]>, AllocError> {
            Allocator::allocate_zeroed(&Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: crate::layout::StdLayout) {
            Allocator::deallocate(&Global, ptr.cast(), layout);
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow(
            &self,
            ptr: NonNull<u8>,
            old_layout: crate::layout::StdLayout,
            new: crate::layout::StdLayout
        ) -> ::core::result::Result<NonNull<[u8]>, AllocError> {
            Allocator::grow(&Global, ptr.cast(), old_layout, new)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow_zeroed(
            &self,
            ptr: NonNull<u8>,
            old_layout: crate::layout::StdLayout,
            new: crate::layout::StdLayout
        ) -> ::core::result::Result<NonNull<[u8]>, AllocError> {
            Allocator::grow_zeroed(&Global, ptr.cast(), old_layout, new)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn shrink(
            &self,
            ptr: NonNull<u8>,
            old_layout: crate::layout::StdLayout,
            new: crate::layout::StdLayout
        ) -> ::core::result::Result<NonNull<[u8]>, AllocError> {
            Allocator::shrink(&Global, ptr.cast(), old_layout, new)
        }
    }

    #[cfg(any(not(feature = "no_alloc"), feature = "std"))]
    default_alloc_impl!(Global);

    // TODO: either Allocator for A: Alloc or vice versa, not sure which. i think i removed that at
    //  some point but i can't remember why.
}
