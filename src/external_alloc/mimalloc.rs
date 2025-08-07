use crate::{
    external_alloc::resize, ffi::mim as ffi, helpers::null_q_zsl_check, Alloc, AllocError,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::NonNull,
};
use libc::c_void;

/// Handle to the mimalloc allocator. This type implements the [`GlobalAlloc`] trait, allowing use
/// as a global allocator, and [`Alloc`](Alloc).
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MiMalloc;

unsafe impl GlobalAlloc for MiMalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ffi::mi_malloc_aligned(layout.size(), layout.align()).cast::<u8>()
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        ffi::mi_free_size_aligned(ptr.cast::<c_void>(), layout.size(), layout.align());
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ffi::mi_zalloc_aligned(layout.size(), layout.align()).cast::<u8>()
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ffi::mi_realloc_aligned(ptr.cast::<c_void>(), new_size, layout.align()).cast::<u8>()
    }
}

#[inline]
fn zsl_check_alloc(
    layout: Layout,
    alloc: unsafe extern "C" fn(usize, usize) -> *mut c_void,
) -> Result<NonNull<u8>, AllocError> {
    null_q_zsl_check(layout, |layout| unsafe {
        alloc(layout.size(), layout.align()).cast::<u8>()
    })
}

impl Alloc for MiMalloc {
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zsl_check_alloc(layout, ffi::mi_malloc_aligned)
    }

    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zsl_check_alloc(layout, ffi::mi_zalloc_aligned)
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            ffi::mi_free_size_aligned(ptr.as_ptr().cast::<c_void>(), layout.size(), layout.align());
        }
    }

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        resize(
            || {
                ffi::mi_realloc_aligned(
                    ptr.as_ptr().cast::<c_void>(),
                    new_layout.size(),
                    new_layout.align(),
                )
            },
            ptr,
            old_layout,
            new_layout,
            false,
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
            || {
                ffi::mi_realloc_aligned(
                    ptr.as_ptr().cast::<c_void>(),
                    new_layout.size(),
                    new_layout.align(),
                )
            },
            ptr,
            old_layout,
            new_layout,
            false,
            false,
        )
    }

    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        _: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        null_q_zsl_check(new_layout, |new_layout| {
            ffi::mi_realloc_aligned(
                ptr.as_ptr().cast::<c_void>(),
                new_layout.size(),
                new_layout.align(),
            )
        })
    }
}
