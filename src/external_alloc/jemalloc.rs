// genuinely no clue how to doc these unsafe blocks
#![allow(clippy::undocumented_unsafe_blocks)]
use crate::{
    error::AllocError,
    external_alloc::{ffi::jem as ffi, REALLOC_DIFF_ALIGN},
    helpers::{nonnull_to_void, null_q_dyn, null_q_zsl_check},
    Alloc,
};
use alloc::alloc::{GlobalAlloc, Layout};
use core::ptr::NonNull;
use libc::c_void;

// TODO: use this elsewhere
macro_rules! assume {
    ($e:expr) => {
        #[cfg(debug_assertions)]
        {
            assert!($e, concat!("assertion failed: ", stringify!($e)));
        }
        if !($e) {
            core::hint::unreachable_unchecked();
        }
    };
}

unsafe fn resize<F: Fn() -> *mut c_void>(
    ralloc: F,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    is_grow: bool,
    nq: fn(*mut c_void, Layout) -> Result<NonNull<u8>, AllocError>,
) -> Result<NonNull<u8>, AllocError> {
    let new_align = new_layout.align();
    let old_align = old_layout.align();

    // TODO: remove if jemalloc supports realloc with diff align
    if new_align != old_align {
        return Err(REALLOC_DIFF_ALIGN);
    }

    let old_size = old_layout.size();
    let new_size = new_layout.size();

    if new_size == old_size && new_align == old_align {
        return Ok(ptr);
    } else if is_grow {
        if new_size < old_size {
            return Err(AllocError::GrowSmallerNewLayout(old_size, new_size));
        }
    } else if new_size > old_size {
        return Err(AllocError::ShrinkBiggerNewLayout(old_size, new_size));
    }

    nq(ralloc(), new_layout)
}

/// Handle to the jemalloc allocator. This type implements the [`GlobalAlloc`] trait, allowing use
/// as a global allocator, and [`Alloc`](Alloc).
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Jemalloc;

fn alloc(layout: Layout) -> *mut c_void {
    unsafe {
        assume!(layout.size() != 0);
    }
    let flags = ffi::layout_to_flags(layout.size(), layout.align());
    if flags == 0 {
        unsafe { ffi::malloc(layout.size()) }
    } else {
        unsafe { ffi::mallocx(layout.size(), flags) }
    }
}

fn zalloc(layout: Layout) -> *mut c_void {
    unsafe {
        assume!(layout.size() != 0);
    }
    let flags = ffi::layout_to_flags(layout.size(), layout.align());
    if flags == 0 {
        unsafe { ffi::calloc(1, layout.size()) }
    } else {
        unsafe { ffi::mallocx(layout.size(), flags | ffi::MALLOCX_ZERO) }
    }
}

unsafe fn dealloc(ptr: *mut u8, layout: Layout) {
    assume!(!ptr.is_null());
    assume!(layout.size() != 0);
    ffi::sdallocx(
        ptr.cast::<c_void>(),
        layout.size(),
        ffi::layout_to_flags(layout.size(), layout.align()),
    );
}

unsafe fn raw_ralloc(ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> *mut c_void {
    assume!(old_layout.size() != 0);
    assume!(new_layout.size() != 0);
    let flags = ffi::layout_to_flags(new_layout.size(), old_layout.align());
    if flags == 0 {
        ffi::realloc(nonnull_to_void(ptr), new_layout.size())
    } else {
        ffi::rallocx(nonnull_to_void(ptr), new_layout.size(), flags)
    }
}

unsafe impl GlobalAlloc for Jemalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        alloc(layout).cast::<u8>()
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        dealloc(ptr, layout);
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        zalloc(layout).cast::<u8>()
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        assume!(!ptr.is_null());
        raw_ralloc(
            NonNull::new_unchecked(ptr),
            layout,
            Layout::from_size_align_unchecked(new_size, layout.align()),
        )
        .cast::<u8>()
    }
}

impl Alloc for Jemalloc {
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        null_q_zsl_check(layout, |layout: Layout| alloc(layout), null_q_dyn)
    }

    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        null_q_zsl_check(layout, |layout: Layout| zalloc(layout), null_q_dyn)
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            dealloc(ptr.as_ptr(), layout);
        }
    }

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        resize(
            || raw_ralloc(ptr, old_layout, new_layout),
            ptr,
            old_layout,
            new_layout,
            true,
            null_q_dyn,
        )
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        // TODO: see if this really needs the same alignment
        resize(
            || raw_ralloc(ptr, old_layout, new_layout),
            ptr,
            old_layout,
            new_layout,
            false,
            null_q_dyn,
        )
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
    /// - [`AllocError::Other`]`("unsupported operation: attempted to reallocate with a different
    ///   alignment")` if `new_layout.align() != old_layout.align()`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.align() != old_layout.align() {
            return Err(REALLOC_DIFF_ALIGN);
        }

        null_q_dyn(raw_ralloc(ptr, old_layout, new_layout), new_layout)
    }
}

#[cfg(feature = "fallible_dealloc")]
impl crate::features::fallible_dealloc::DeallocUnchecked for Jemalloc {
    #[inline]
    unsafe fn dealloc_unchecked(&self, ptr: NonNull<u8>, layout: Layout) {
        dealloc(ptr.as_ptr(), layout);
    }
}
