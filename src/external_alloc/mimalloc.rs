use crate::{
    ffi::mim as ffi,
    helpers::{dangling_nonnull_for, null_q},
    Alloc, AllocError,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::NonNull,
};

/// Handle to the mimalloc allocator. This type implements the [`GlobalAlloc`] trait, allowing use
/// as a global allocator, and [`Alloc`](Alloc).
pub struct MiMalloc;

unsafe impl GlobalAlloc for MiMalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ffi::mi_malloc_aligned(layout.size(), layout.align()).cast()
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        ffi::mi_free_size_aligned(ptr.cast(), layout.size(), layout.align());
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ffi::mi_zalloc_aligned(layout.size(), layout.align()).cast()
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ffi::mi_realloc_aligned(ptr.cast(), new_size, layout.align()).cast()
    }
}

impl Alloc for MiMalloc {
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        if layout.size() == 0 {
            Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
        } else {
            null_q(
                unsafe { ffi::mi_malloc_aligned(layout.size(), layout.align()) }.cast::<u8>(),
                layout,
            )
        }
    }

    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        if layout.size() == 0 {
            Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
        } else {
            null_q(
                unsafe { ffi::mi_zalloc_aligned(layout.size(), layout.align()) }.cast::<u8>(),
                layout,
            )
        }
    }

    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            ffi::mi_free_size_aligned(ptr.as_ptr().cast(), layout.size(), layout.align());
        }
    }

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.size() < old_layout.size() {
            return Err(AllocError::GrowSmallerNewLayout(
                old_layout.size(),
                new_layout.size(),
            ));
        } else if new_layout.size() == old_layout.size() {
            return Ok(ptr);
        }
        null_q(
            ffi::mi_realloc_aligned(ptr.as_ptr().cast(), new_layout.size(), new_layout.align()),
            new_layout,
        )
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.size() > old_layout.size() {
            return Err(AllocError::ShrinkBiggerNewLayout(
                old_layout.size(),
                new_layout.size(),
            ));
        } else if new_layout.size() == old_layout.size() {
            return Ok(ptr);
        }
        null_q(
            ffi::mi_realloc_aligned(ptr.as_ptr().cast(), new_layout.size(), new_layout.align()),
            new_layout,
        )
    }

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
