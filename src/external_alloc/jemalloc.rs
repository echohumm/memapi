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

unsafe impl GlobalAlloc for Jemalloc {
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        let flags = ffi::layout_to_flags(layout.size(), layout.align());
        (if flags == 0 {
            ffi::malloc(layout.size())
        } else {
            ffi::mallocx(layout.size(), flags)
        }).cast::<u8>()
    }

    #[cfg_attr(miri, track_caller)]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        assume!(!ptr.is_null());
        assume!(layout.size() != 0);
        ffi::sdallocx(
            ptr.cast::<c_void>(),
            layout.size(),
            ffi::layout_to_flags(layout.size(), layout.align()),
        );
    }

    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        let flags = ffi::layout_to_flags(layout.size(), layout.align());
        (if flags == 0 {
            ffi::calloc(1, layout.size())
        } else {
            ffi::mallocx(layout.size(), flags | ffi::MALLOCX_ZERO)
        }).cast::<u8>()
    }

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
    #[cfg_attr(miri, track_caller)]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        null_q_zsl_check(layout, |layout: Layout| {
            let flags = ffi::layout_to_flags(layout.size(), layout.align());
            if flags == 0 {
                unsafe { ffi::malloc(layout.size()) }
            } else {
                unsafe { ffi::mallocx(layout.size(), flags) }
            }
        })
    }

    #[cfg_attr(miri, track_caller)]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        null_q_zsl_check(layout, |layout: Layout| {
            let flags = ffi::layout_to_flags(layout.size(), layout.align());
            if flags == 0 {
                unsafe { ffi::calloc(1, layout.size()) }
            } else {
                unsafe { ffi::mallocx(layout.size(), flags | ffi::MALLOCX_ZERO) }
            }
        })
    }

    #[cfg_attr(miri, track_caller)]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            ffi::sdallocx(
                ptr.as_ptr().cast::<c_void>(),
                layout.size(),
                ffi::layout_to_flags(layout.size(), layout.align()),
            );
        }
    }

    #[cfg_attr(miri, track_caller)]
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

    #[cfg_attr(miri, track_caller)]
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
    #[cfg_attr(miri, track_caller)]
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
