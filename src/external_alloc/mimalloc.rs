use crate::{
    external_alloc::resize,
    ffi::mim as ffi,
    helpers::{null_q, zsl_check},
    Alloc, AllocError,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    ffi::c_void,
    ptr::NonNull,
};

/// Handle to the mimalloc allocator. This type implements the [`GlobalAlloc`] trait, allowing use
/// as a global allocator, and [`Alloc`](Alloc).
pub struct MiMalloc;

unsafe impl GlobalAlloc for MiMalloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ffi::mi_malloc_aligned(layout.size(), layout.align()).cast()
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        ffi::mi_free_size_aligned(ptr.cast(), layout.size(), layout.align());
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ffi::mi_zalloc_aligned(layout.size(), layout.align()).cast()
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ffi::mi_realloc_aligned(ptr.cast(), new_size, layout.align()).cast()
    }
}

#[cfg_attr(miri, track_caller)]
#[inline]
fn zsl_check_alloc(
    layout: Layout,
    alloc: unsafe extern "C" fn(usize, usize) -> *mut c_void,
) -> Result<NonNull<u8>, AllocError> {
    zsl_check(layout, |layout: Layout| {
        null_q(
            unsafe { alloc(layout.size(), layout.align()) }.cast::<u8>(),
            layout,
        )
    })
}

impl Alloc for MiMalloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zsl_check_alloc(layout, ffi::mi_malloc_aligned)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zsl_check_alloc(layout, ffi::mi_zalloc_aligned)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            ffi::mi_free_size_aligned(ptr.as_ptr().cast(), layout.size(), layout.align());
        }
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        resize(
            || unsafe {
                ffi::mi_realloc_aligned(ptr.as_ptr().cast(), new_layout.size(), new_layout.align())
            },
            ptr,
            old_layout,
            new_layout,
            false,
            true,
        )
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        resize(
            || unsafe {
                ffi::mi_realloc_aligned(ptr.as_ptr().cast(), new_layout.size(), new_layout.align())
            },
            ptr,
            old_layout,
            new_layout,
            false,
            false,
        )
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        _: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        null_q(
            ffi::mi_realloc_aligned(ptr.as_ptr().cast(), new_layout.size(), new_layout.align()),
            new_layout,
        )
    }
}
