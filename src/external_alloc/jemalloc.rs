use crate::{
    error::AllocError,
    external_alloc::REALLOC_DIFF_ALIGN,
    external_alloc::{ffi::jem as ffi, resize},
    helpers::{null_q, null_q_zsl_check},
    Alloc,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::NonNull,
};
use libc::c_void;

macro_rules! assume {
    ($e:expr) => {
        debug_assert!($e);
        if !($e) {
            core::hint::unreachable_unchecked();
        }
    };
}

/// Handle to the jemalloc allocator. This type implements the [`GlobalAlloc`] trait, allowing use
/// as a global allocator, and [`Alloc`](Alloc).
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Jemalloc;

fn alloc(layout: Layout) -> *mut c_void {
    let flags = ffi::layout_to_flags(layout.size(), layout.align());
    if flags == 0 {
        unsafe { ffi::malloc(layout.size()) }
    } else {
        unsafe { ffi::mallocx(layout.size(), flags) }
    }
}

fn alloc_zeroed(layout: Layout) -> *mut c_void {
    let flags = ffi::layout_to_flags(layout.size(), layout.align());
    if flags == 0 {
        unsafe { ffi::calloc(1, layout.size()) }
    } else {
        unsafe { ffi::mallocx(layout.size(), flags | ffi::MALLOCX_ZERO) }
    }
}

unsafe fn dealloc(ptr: *mut u8, layout: Layout) {
    ffi::sdallocx(
        ptr.cast::<c_void>(),
        layout.size(),
        ffi::layout_to_flags(layout.size(), layout.align()),
    );
}

unsafe impl GlobalAlloc for Jemalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        alloc(layout).cast::<u8>()
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        assume!(!ptr.is_null());
        assume!(layout.size() != 0);
        dealloc(ptr, layout);
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        alloc_zeroed(layout).cast::<u8>()
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        assume!(layout.size() != 0);
        assume!(new_size != 0);
        let flags = ffi::layout_to_flags(new_size, layout.align());
        let p = ptr.cast::<c_void>();
        (if flags == 0 {
            ffi::realloc(p, new_size)
        } else {
            ffi::rallocx(p, new_size, flags)
        }).cast::<u8>()
    }
}

impl Alloc for Jemalloc {
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        null_q_zsl_check(layout, |layout: Layout| {
            alloc(layout)
        })
    }

    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        null_q_zsl_check(layout, |layout: Layout| {
            alloc_zeroed(layout)
        })
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
            || ffi::raw_ralloc(ptr.as_ptr().cast::<c_void>(), old_layout, new_layout),
            ptr,
            old_layout,
            new_layout,
            true,
            true,
        )
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        resize(
            || ffi::raw_ralloc(ptr.as_ptr().cast::<c_void>(), old_layout, new_layout),
            ptr,
            old_layout,
            new_layout,
            true,
            false,
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
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.align() != old_layout.align() {
            return Err(AllocError::Other(REALLOC_DIFF_ALIGN));
        }
        null_q(
            ffi::raw_ralloc(ptr.as_ptr().cast::<c_void>(), old_layout, new_layout),
            new_layout,
        )
    }
}
