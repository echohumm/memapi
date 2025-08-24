//! `memapi` provides a `no_std`-friendly memory allocation interface
//! for managing raw buffers, suitable for use in collections.
//!
//! This crate exports:
//!
//! - [`Alloc`]: a trait defining basic allocation, deallocation, grow, and shrink operations.
//! - [`DefaultAlloc`]: a zero-cost wrapper delegating to the global allocator.
//! - [`AllocError`]: an enum representing allocation failure cases.
//! - [`PtrProps`](data::type_props::PtrProps): property getters for pointers to values.
//! - [`SizedProps`](data::type_props::SizedProps): properties for sized types, similar to the unstable,
//!   hidden [`SizedTypeProperties`](core::mem::SizedTypeProperties).
//! - [`VarSized`](data::type_props::VarSized): a marker trait for types with `usize` metadata.
//! - [`UnsizedCopy`](data::marker::UnsizedCopy): a marker trait for safe copying of unsized values.
//! - [`Thin`](data::marker::Thin): a marker trait for pointers without metadata.
//!
//! # Features
//!
//! - **`no_alloc`**: Removes the [`alloc`] dependency.
//!
//! - **`malloc_defaultalloc`**: Uses libc's malloc for `DefaultAlloc`.
//!
//! - **`alloc_ext`**: Adds the [`AllocExt`] trait for ergonomic allocator abstractions.
//!
//! - **`alloc_slice`**: Provides slice-based extensions:
//!   - [`AllocSlice`] for basic slice operations.
//!   - (With `alloc_ext`) [`AllocSliceExt`] for advanced slice abstractions.
//!   - (With `alloc_slice_extend`) [`AllocExtendSlice`]
//!
//! - **`stats`**: Collection of allocation statistics utilities:
//!   - [`StatsLogger`](stats::StatsLogger), a thread-safe logger for allocation events.
//!   - [`Stats`](stats::Stats), an allocator wrapper that logs operations.
//!   - [`AllocRes`](stats::AllocRes), [`AllocStat`](stats::AllocStat),
//!     [`MemoryRegion`](stats::MemoryRegion), [`ResizeMemRegions`](stats::ResizeMemRegions),
//!     [`AllocKind`](stats::AllocKind) types.
//!   - (With `std`) Several default logger implementations.
//!   - (With `stats_file_lock`) Safer file locking for `FileLog`. (MSRV ≥ 1.89.0).
//!   - (With `stats_thread_safe_io`) [`ThreadSafeIOLogger`](stats::ThreadSafeIOLog) for logging to
//!     [lockable](stats::WriteLock) writers. (MSRV ≥ 1.61.0)
//!   - (With `stats_parking_lot`) Usage of [`parking_lot::Mutex`] instead of [`std::sync::Mutex`].
//!
//! - **`fallible_dealloc`**: Adds [`CheckedDealloc`], a trait for fallible deallocations.
//!   - (With `alloc_slice`): [`CheckedDeallocSlice`], a trait for slice-based fallible deallocation
//!     extensions.
//!
//! - **`alloc_aligned_at`**: Adds [`AllocAlignedAt`](AllocAlignedAt), a trait for allocating such
//!   that the actual pointer isn't aligned until after an offset.
//!
//! - **`external_alloc`**: FFI helpers for external allocators.
//!
//! - **`os_err_reporting`**: Enables OS error reporting on failed allocation for supported
//!   allocators.
//!   - Supported allocators: Jemalloc, Rust's default, Malloc, `MiMalloc` if
//!     `mimalloc_err_reporting` is enabled.
//!
//! - **`jemalloc`**: Provides [`Jemalloc`](jemalloc::Jemalloc), a ZST `Alloc` implementation using
//!   `Jemallocator`.
//!
//! - **`mimalloc`**: Provides [`MiMalloc`](mimalloc::MiMalloc), a ZST `Alloc` implementation using
//!   `MiMalloc`.
//!   - **`mimalloc_err_reporting`**: Enables OS error reporting on failed allocation for
//!     `MiMalloc`.
//!   - **`mimalloc_global_err`**: Enables use of a global atomic for transferring the thread-local
//!     error state to a global error state.
//!   - **`mimalloc_err_output`**: Enables OS error reporting AND printing to stderr on failed
//!     allocation for `MiMalloc`.
//!
//! - **`malloc`**: Provides [`Malloc`](libc_malloc::Malloc), a ZST `Alloc` implementation using
//!   `libc`'s platform bindings to allocation functions.
//!
//! - **`nightly`**: Enables using the unstable `allocator_api`.
//!
//! - **`metadata`, `clone_to_uninit`, `sized_hierarchy`**: Enable using the nightly Rust feature of
//!   the same name.
//!
//! - **`assumptions`**: Enables use of `debug_assert!` and `core::hint::unreachable_unchecked()` in
//!   certain functions to "assume" a condition is true, for safety and optimizations. 
//!   (MSRV ≥ 1.57.0)
//!
//! - **`const_extras`**: Enables additional `const` methods (MSRV ≥ 1.61.0).
//!
//! - **`c_str`**: Implements `UnsizedCopy` for `core::ffi::CStr` (MSRV ≥ 1.64.0).
//!
//! - **`const_max`**: Further expands `const` support (MSRV ≥ 1.83.0).
//!
//! All other features are bindings to `MiMalloc`/`Jemalloc`'s features. Consult their documentation
//! for more information.

// TODO: more allocators, work on underlying allocators ffi

// TODO: reduce compilation times (see stdlib's versions of our stuff like layout)

// TODO: add more tests

// TODO: test on other platforms/targets

#![allow(unknown_lints)]
#![warn(clippy::all, clippy::pedantic, clippy::borrow_as_ptr, clippy::undocumented_unsafe_blocks)]
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
#![cfg_attr(feature = "sized_hierarchy", feature(sized_hierarchy))]

// TODO: generally add more helpers and dedup to reduce bin size

// TODO: add missing cfg_attr(miri, track_caller) attributes, remove unnecessary ones

// TODO: consistent attribute and doc orderings

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
    (AllocError::$n:ident($($fallible:expr)+)) => {
        match $($fallible)+ {
            Ok(s) => s,
            Err(e) => return Err(crate::error::AllocError::$n(e)),
        }
    };
    (lay, $sz:expr, $aln:expr) => {
        match crate::unstable_util::lay_from_size_align($sz, $aln) {
            Ok(layout) => layout,
            Err(e) => return Err(
                crate::error::AllocError::InvalidLayout(crate::error::InvLayout($sz, $aln, e))
            ),
        }
    };
    (lay_preproc $layout:ident) => {{
        let pre = preproc_layout($layout);
        match pre {
            Ok(layout) => layout,
            Err(e) => return Err(crate::error::AllocError::InvalidLayout(e)),
        }
    }}
}

#[allow(unused_macros)]
macro_rules! assume {
    // TODO: dont need both of these if i just remove one's usages
    ($e:expr) => {
        #[cfg(feature = "assumptions")]
        {
            let res = $e;

            #[cfg(debug_assertions)]
            {
                assert!(res, concat!("assertion failed: ", stringify!($e)));
            }
            crate::assert_unreachable(res);
        }
    };
    (u_pre $e:expr, $msg:literal) => {
        #[cfg(feature = "assumptions")]
        {
            let res = $e;
            #[cfg(debug_assertions)]
            {
                assert!(
                    res,
                    concat!("unsafe precondition `", stringify!($e), "` violated: ", $msg)
                );
            }
            crate::assert_unreachable(res);
        }
    };
}

/// Asserts a boolean value to be true, and the false condition to be unreachable.
///
/// # Safety
///
/// This is only safe to call if `cond` is `true`. See
/// [`unreachable_unchecked`](core::hint::unreachable_unchecked) for more details.
#[cfg_attr(not(feature = "dev"), doc(hidden))]
pub const unsafe fn assert_unreachable(cond: bool) {
    if !cond {
        #[allow(clippy::incompatible_msrv)]
        core::hint::unreachable_unchecked();
    }
}

// TODO: dedup docs with some macros
// TODO: split crate into smaller crates (memapi-jemalloc, memapi-mimalloc, etc.)
// TODO: simplify cfgs and make sure they are correct

#[cfg(not(feature = "no_alloc"))] extern crate alloc;
extern crate core;

#[cfg(feature = "no_alloc")] mod layout;

#[cfg(not(feature = "no_alloc"))] pub use alloc::alloc::Layout;

#[cfg(feature = "no_alloc")] pub use layout::Layout;

#[cfg(feature = "extern_alloc")]
/// External allocator support.
///
/// This module includes FFI for other allocators and types that implement [`Alloc`] for each.
pub mod external;

#[cfg(any(
    feature = "alloc_ext",
    feature = "alloc_slice",
    feature = "resize_in_place",
    feature = "alloc_aligned_at",
    feature = "stats",
    feature = "checked_dealloc",
))]
mod features;

#[cfg(feature = "alloc_ext")] pub use features::alloc_ext::*;
#[cfg(feature = "alloc_slice")] pub use features::alloc_slice::*;
#[cfg(feature = "checked_dealloc")] pub use features::checked_dealloc;
#[cfg(feature = "resize_in_place")] pub use features::resize_in_place::*;
#[cfg(any(feature = "stats", feature = "alloc_aligned_at",))] pub use features::*;

// TODO: better docs and name
/// Module for anything related specifically to data.
/// 
/// This includes marker traits, type properties, and miscellaneous data-handling traits.
pub mod data;

/// Small alternatives to Rust functions that are unstable as of the most recent release.
pub mod unstable_util;

/// Errors that can occur during allocation.
pub mod error;

use {
    core::{
        cmp::Ordering,
        ptr::{self, NonNull}
    },
    error::AllocError,
    helpers::alloc_then
};

#[cfg(any(not(feature = "no_alloc"), feature = "malloc_defaultalloc"))]
/// Default allocator, delegating to the global allocator.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefaultAlloc;

#[allow(unused_macros)]
macro_rules! default_alloc_impl {
    ($ty:ty) => {
        #[cfg(not(feature = "malloc_defaultalloc"))]
        impl crate::Alloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn alloc(
                &self,
                layout: crate::Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::helpers::null_q_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non zero-sized before use.
                    |layout| unsafe { alloc::alloc::alloc(layout) },
                    crate::helpers::null_q_dyn
                )
            }

            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn zalloc(
                &self,
                layout: crate::Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::helpers::null_q_zsl_check(
                    layout,
                    // SAFETY: we check the layout is non zero-sized before use.
                    |layout| unsafe { alloc::alloc::alloc_zeroed(layout) },
                    crate::helpers::null_q_dyn
                )
            }

            #[cfg_attr(miri, track_caller)]
            #[inline]
            unsafe fn dealloc(&self, ptr: core::ptr::NonNull<u8>, layout: crate::Layout) {
                if layout.size() != 0 {
                    alloc::alloc::dealloc(ptr.as_ptr(), layout);
                }
            }
        }

        #[cfg(feature = "malloc_defaultalloc")]
        impl crate::Alloc for $ty {
            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn alloc(
                &self,
                layout: crate::Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::external::ffi::libc::alloc(layout)
            }

            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn zalloc(
                &self,
                layout: crate::Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::external::ffi::libc::zalloc(layout)
            }

            #[cfg_attr(miri, track_caller)]
            #[inline]
            unsafe fn dealloc(&self, ptr: core::ptr::NonNull<u8>, layout: crate::Layout) {
                crate::external::ffi::libc::dealloc(ptr, layout);
            }

            #[cfg_attr(miri, track_caller)]
            #[inline]
            unsafe fn grow(
                &self,
                ptr: core::ptr::NonNull<u8>,
                old_layout: crate::Layout,
                new_layout: crate::Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::external::ffi::libc::grow(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            unsafe fn zgrow(
                &self,
                ptr: core::ptr::NonNull<u8>,
                old_layout: crate::Layout,
                new_layout: crate::Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::external::ffi::libc::zgrow(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            unsafe fn shrink(
                &self,
                ptr: core::ptr::NonNull<u8>,
                old_layout: crate::Layout,
                new_layout: crate::Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::external::ffi::libc::shrink(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            unsafe fn realloc(
                &self,
                ptr: core::ptr::NonNull<u8>,
                old_layout: crate::Layout,
                new_layout: crate::Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::external::ffi::libc::realloc_helper(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            unsafe fn rezalloc(
                &self,
                ptr: core::ptr::NonNull<u8>,
                old_layout: crate::Layout,
                new_layout: crate::Layout
            ) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
                crate::external::ffi::libc::rezalloc(ptr, old_layout, new_layout)
            }
        }
    };
}

#[cfg(all(not(feature = "no_alloc"), not(feature = "malloc_defaultalloc")))]
// SAFETY: DefaultAlloc doesn't unwind, and all layout operations are correct
unsafe impl alloc::alloc::GlobalAlloc for DefaultAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 { alloc::alloc::alloc(layout) }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) { alloc::alloc::dealloc(ptr, layout); }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 { alloc::alloc::alloc_zeroed(layout) }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        alloc::alloc::realloc(ptr, layout, new_size)
    }
}

#[cfg(all(not(feature = "no_alloc"), feature = "malloc_defaultalloc"))]
// SAFETY: Malloc doesn't unwind, and all layout operations are correct
unsafe impl alloc::alloc::GlobalAlloc for DefaultAlloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 { external::ffi::libc::raw_alloc(layout) }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        external::ffi::libc::raw_dealloc(ptr, layout);
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        external::ffi::libc::raw_zalloc(layout)
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        external::ffi::libc::raw_realloc(ptr, layout, new_size)
    }
}

#[cfg(any(not(feature = "no_alloc"), feature = "malloc_defaultalloc"))]
default_alloc_impl!(DefaultAlloc);

// MAYBEDO: split this trait into multiple:
//  - Alloc
//  - Dealloc
//  - Grow: Alloc + Dealloc
//  - Shrink: Alloc + Dealloc
//  - Realloc: Grow + Shrink
//  and a supertrait:
//  - BasicAlloc: Alloc + Dealloc
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
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        // SAFETY: alloc returns at least layout.size() allocated bytes
        unsafe {
            alloc_then(self, layout, (), |p, ()| {
                ptr::write_bytes(p.as_ptr(), 0, layout.size());
                p
            })
        }
    }

    /// Deallocates a previously allocated block.
    ///
    /// This is a noop if `layout.size() == 0`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `layout` must describe exactly the same block.
    ///
    /// # Panics
    ///
    /// Some implementations may choose to panic if `ptr` or `layout` are invalid.
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout);

    /// Grow the given block to a new, larger layout.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// On failure, the original memory won't be deallocated or modified.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        grow(self, ptr, old_layout, new_layout, AllocPattern::Uninitialized)
    }

    /// Grows the given block to a new, larger layout, zeroing any newly allocated bytes.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] in `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// On failure, the original memory won't be deallocated or modified.
    #[cfg_attr(miri, track_caller)]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        grow(self, ptr, old_layout, new_layout, AllocPattern::Zeroed)
    }

    /// Shrink the given block to a new, smaller layout.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ShrinkLargerNewLayout`] if `new_layout.size() > old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// On failure, the original memory won't be deallocated or modified.
    #[cfg_attr(miri, track_caller)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        shrink(self, ptr, old_layout, new_layout)
    }

    /// Reallocates a block, growing or shrinking as needed.
    ///
    ///
    /// On grow, preserves existing contents up to `old_layout.size()`, and
    /// on shrink, truncates to `new_layout.size()`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// On failure, the original memory won't be deallocated or modified.
    #[cfg_attr(miri, track_caller)]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        ralloc(self, ptr, old_layout, new_layout, AllocPattern::Uninitialized)
    }

    /// Reallocates a block, growing or shrinking as needed, zeroing any newly
    /// allocated bytes.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// On failure, the original memory won't be deallocated or modified.
    #[cfg_attr(miri, track_caller)]
    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        ralloc(self, ptr, old_layout, new_layout, AllocPattern::Zeroed)
    }
}

#[cfg(feature = "nightly")]
/// The primary module for when `nightly` is enabled.
pub(crate) mod nightly {
    #[cfg(not(feature = "no_alloc"))]
    // SAFETY: DefaultAlloc's allocated memory isn't deallocated until a deallocation method is
    //  called. as a ZST allocator, copying/cloning it doesn't change behavior or invalidate
    //  allocations.
    unsafe impl alloc::alloc::Allocator for crate::DefaultAlloc {
        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate(
            &self,
            layout: crate::Layout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::allocate(&alloc::alloc::Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        fn allocate_zeroed(
            &self,
            layout: crate::Layout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::allocate_zeroed(&alloc::alloc::Global, layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn deallocate(&self, ptr: core::ptr::NonNull<u8>, layout: crate::Layout) {
            alloc::alloc::Allocator::deallocate(&alloc::alloc::Global, ptr.cast(), layout);
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow(
            &self,
            ptr: core::ptr::NonNull<u8>,
            old_layout: crate::Layout,
            new_layout: crate::Layout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::grow(&alloc::alloc::Global, ptr.cast(), old_layout, new_layout)
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        unsafe fn grow_zeroed(
            &self,
            ptr: core::ptr::NonNull<u8>,
            old_layout: crate::Layout,
            new_layout: crate::Layout
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
            old_layout: crate::Layout,
            new_layout: crate::Layout
        ) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
            alloc::alloc::Allocator::shrink(
                &alloc::alloc::Global,
                ptr.cast(),
                old_layout,
                new_layout
            )
        }
    }

    #[cfg(not(feature = "no_alloc"))]
    default_alloc_impl!(alloc::alloc::Global);
}

#[allow(clippy::inline_always)]
impl<A: Alloc + ?Sized> Alloc for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> { (**self).alloc(layout) }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> { (**self).zalloc(layout) }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) { (**self).dealloc(ptr, layout); }
}

#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Alloc for std::alloc::System {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        helpers::null_q_zsl_check(
            layout,
            // SAFETY: System::alloc is only called after the layout is verified non-zero-sized.
            |layout| unsafe { alloc::alloc::GlobalAlloc::alloc(self, layout) },
            helpers::null_q_dyn
        )
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        helpers::null_q_zsl_check(
            layout,
            // SAFETY: System::alloc_zeroed is only called after the layout is verified
            //  non-zero-sized.
            |layout| unsafe { alloc::alloc::GlobalAlloc::alloc_zeroed(self, layout) },
            helpers::null_q_dyn
        )
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            alloc::alloc::GlobalAlloc::dealloc(self, ptr.as_ptr(), layout);
        }
    }
}

/// Internal helper to grow the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`, filling new bytes using `pattern.`
#[allow(clippy::missing_errors_doc, clippy::missing_safety_doc)]
#[cfg_attr(not(feature = "dev"), doc(hidden))]
#[cfg_attr(miri, track_caller)]
pub unsafe fn grow<A: Alloc + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern
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
        Ordering::Greater => Err(AllocError::grow_smaller(old_layout.size(), new_layout.size()))
    }
}

/// Internal helper to shrink the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
#[allow(clippy::missing_errors_doc, clippy::missing_safety_doc)]
#[cfg_attr(not(feature = "dev"), doc(hidden))]
#[cfg_attr(miri, track_caller)]
pub unsafe fn shrink<A: Alloc + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout
) -> Result<NonNull<u8>, AllocError> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => Err(AllocError::shrink_larger(old_layout.size(), new_layout.size())),
        Ordering::Equal => {
            if new_layout.align() == old_layout.align() {
                Ok(ptr)
            } else {
                shrink_unchecked(&a, ptr, old_layout, new_layout)
            }
        }
        Ordering::Greater => shrink_unchecked(a, ptr, old_layout, new_layout)
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
unsafe fn grow_unchecked<A: Alloc + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern
) -> Result<NonNull<u8>, AllocError> {
    let old_size = old_layout.size();
    let new_ptr = match pattern {
        AllocPattern::Uninitialized => tri!(do a.alloc(new_layout)),
        AllocPattern::Zeroed => tri!(do a.zalloc(new_layout)),
        #[cfg(feature = "alloc_ext")]
        AllocPattern::Filled(n) => {
            let mem = tri!(do a.alloc(new_layout));
            ptr::write_bytes(mem.as_ptr().add(old_size), n, new_layout.size() - old_size);
            mem
        }
        AllocPattern::Shrink => core::hint::unreachable_unchecked()
    };

    ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);
    if old_size != 0 {
        a.dealloc(ptr, old_layout);
    }

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
    new_layout: Layout
) -> Result<NonNull<u8>, AllocError> {
    let new_ptr = tri!(do a.alloc(new_layout));

    ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_layout.size());
    if old_layout.size() != 0 {
        a.dealloc(ptr, old_layout);
    }

    Ok(new_ptr)
}

/// Helper for realloc to reduce repetition.
#[allow(clippy::missing_errors_doc, clippy::missing_safety_doc)]
#[cfg_attr(not(feature = "dev"), doc(hidden))]
#[cfg_attr(miri, track_caller)]
pub unsafe fn ralloc<A: Alloc + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pat: AllocPattern
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

/// A byte pattern.
///
/// This is used to determine or represent the pattern new bytes will be or were filled with.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "dev"), doc(hidden))]
#[repr(u8)]
pub enum AllocPattern {
    /// Uninitialized bytes.
    Uninitialized,
    /// Zeroed bytes.
    Zeroed,
    #[cfg(feature = "alloc_ext")]
    /// Bytes filled with a specific value.
    Filled(u8),
    /// No new bytes.
    Shrink
}

/// Helpers that tend to be useful in other libraries as well.
pub mod helpers;
