use crate::{
    external::ffi::libc::{alloc, dealloc, grow, realloc_helper, rezalloc, shrink, zalloc, zgrow},
    Alloc, AllocError, Layout,
};
use core::ptr::NonNull;

#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// Handle to libc's allocation functions. This type implements the [`GlobalAlloc`] trait, allowing
/// use as a global allocator, and [`Alloc`](Alloc).
///
/// This is almost the same as [`System`](std::alloc::System).
///
/// Note that, in addition to the usual requirement of alignments being a
/// [power of two](usize::is_power_of_two), this allocator requires that `align` is a multiple of
/// [`usize::SZ`](crate::type_props::SizedProps::SZ), AKA the size of C's *void.
pub struct Malloc;

#[cfg(not(feature = "no_alloc"))]
// SAFETY: `Malloc` doesn't unwind, and layouts are correct
unsafe impl alloc::alloc::GlobalAlloc for Malloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        crate::external::ffi::libc::raw_alloc(layout)
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        crate::external::ffi::libc::raw_dealloc(ptr, layout);
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        crate::external::ffi::libc::raw_zalloc(layout)
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        crate::external::ffi::libc::raw_realloc(ptr, layout, new_size)
    }
}

impl Alloc for Malloc {
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        alloc(layout)
    }

    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zalloc(layout)
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        dealloc(ptr, layout);
    }

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        grow(ptr, old_layout, new_layout)
    }

    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        zgrow(ptr, old_layout, new_layout)
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        shrink(ptr, old_layout, new_layout)
    }

    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        realloc_helper(ptr, old_layout, new_layout)
    }

    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        rezalloc(ptr, old_layout, new_layout)
    }
}
