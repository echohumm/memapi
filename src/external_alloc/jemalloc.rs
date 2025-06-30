use crate::helpers::zsl_check;
use crate::{
    error::{AllocError, UOp},
    external_alloc::{ffi::jem as ffi, resize},
    helpers::null_q,
    Alloc,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::NonNull,
};

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
#[derive(Copy, Clone, Default, Debug)]
pub struct Jemalloc;

unsafe impl GlobalAlloc for Jemalloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        let flags = ffi::layout_to_flags(layout.size(), layout.align());
        if flags == 0 {
            ffi::malloc(layout.size())
        } else {
            ffi::mallocx(layout.size(), flags)
        }
        .cast()
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        assume!(!ptr.is_null());
        assume!(layout.size() != 0);
        ffi::sdallocx(
            ptr.cast(),
            layout.size(),
            ffi::layout_to_flags(layout.size(), layout.align()),
        );
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        let flags = ffi::layout_to_flags(layout.size(), layout.align());
        if flags == 0 {
            ffi::calloc(1, layout.size())
        } else {
            ffi::mallocx(layout.size(), flags | ffi::MALLOCX_ZERO)
        }
        .cast()
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        assume!(layout.size() != 0);
        assume!(new_size != 0);
        let flags = ffi::layout_to_flags(new_size, layout.align());
        if flags == 0 {
            ffi::realloc(ptr.cast(), new_size)
        } else {
            ffi::rallocx(ptr.cast(), new_size, flags)
        }
        .cast()
    }
}

impl Alloc for Jemalloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zsl_check(layout, |layout| {
            let flags = ffi::layout_to_flags(layout.size(), layout.align());
            null_q(
                if flags == 0 {
                    unsafe { ffi::malloc(layout.size()) }
                } else {
                    unsafe { ffi::mallocx(layout.size(), flags) }
                },
                layout,
            )
        })
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zsl_check(layout, |layout| {
            let flags = ffi::layout_to_flags(layout.size(), layout.align());
            null_q(
                if flags == 0 {
                    unsafe { ffi::calloc(1, layout.size()) }
                } else {
                    unsafe { ffi::mallocx(layout.size(), flags | crate::ffi::jem::MALLOCX_ZERO) }
                },
                layout,
            )
        })
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            ffi::sdallocx(
                ptr.as_ptr().cast(),
                layout.size(),
                ffi::layout_to_flags(layout.size(), layout.align()),
            );
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
            || unsafe { ffi::raw_ralloc(ptr.as_ptr().cast(), old_layout, new_layout) },
            ptr,
            old_layout,
            new_layout,
            true,
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
            || unsafe { ffi::raw_ralloc(ptr.as_ptr().cast(), old_layout, new_layout) },
            ptr,
            old_layout,
            new_layout,
            true,
            false,
        )
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.align() != old_layout.align() {
            return Err(AllocError::UnsupportedOperation(UOp::ReallocDiffAlign(
                old_layout.align(),
                new_layout.align(),
            )));
        }
        null_q(
            ffi::raw_ralloc(ptr.as_ptr().cast(), old_layout, new_layout),
            new_layout,
        )
    }
}
