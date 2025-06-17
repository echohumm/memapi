use crate::{
    external_alloc::ffi::jem::{self as ffi, layout_to_flags},
    helpers::dangling_nonnull_for,
    null_q, Alloc, AllocError, UOp,
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
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        let flags = layout_to_flags(layout.size(), layout.align());
        if flags == 0 {
            ffi::malloc(layout.size())
        } else {
            ffi::mallocx(layout.size(), flags)
        }
        .cast()
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        assume!(!ptr.is_null());
        assume!(layout.size() != 0);
        ffi::sdallocx(
            ptr.cast(),
            layout.size(),
            layout_to_flags(layout.size(), layout.align()),
        );
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        let flags = layout_to_flags(layout.size(), layout.align());
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
        let flags = layout_to_flags(new_size, layout.align());
        if flags == 0 {
            ffi::realloc(ptr.cast(), new_size)
        } else {
            ffi::rallocx(ptr.cast(), new_size, flags)
        }
        .cast()
    }
}

impl Alloc for Jemalloc {
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        if layout.size() == 0 {
            Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
        } else {
            let flags = layout_to_flags(layout.size(), layout.align());
            null_q(
                if flags == 0 {
                    unsafe { ffi::malloc(layout.size()) }
                } else {
                    unsafe { ffi::mallocx(layout.size(), flags) }
                },
                layout,
            )
        }
    }

    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        if layout.size() == 0 {
            Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
        } else {
            let flags = layout_to_flags(layout.size(), layout.align());
            null_q(
                if flags == 0 {
                    unsafe { ffi::calloc(1, layout.size()) }
                } else {
                    unsafe { ffi::mallocx(layout.size(), flags | crate::ffi::jem::MALLOCX_ZERO) }
                },
                layout,
            )
        }
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            ffi::sdallocx(
                ptr.as_ptr().cast(),
                layout.size(),
                layout_to_flags(layout.size(), layout.align()),
            );
        }
    }

    #[inline]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.align() != old_layout.align() {
            return Err(AllocError::UnsupportedOperation(
                UOp::ReallocDifferentAlign(old_layout.align(), new_layout.align()),
            ));
        } else if new_layout.size() < old_layout.size() {
            return Err(AllocError::GrowSmallerNewLayout(
                old_layout.size(),
                new_layout.size(),
            ));
        } else if new_layout.size() == old_layout.size() {
            return Ok(ptr);
        }
        null_q(
            ffi::raw_ralloc(ptr.as_ptr().cast(), old_layout, new_layout),
            new_layout,
        )
    }

    #[inline]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.align() != old_layout.align() {
            return Err(AllocError::UnsupportedOperation(
                UOp::ReallocDifferentAlign(old_layout.align(), new_layout.align()),
            ));
        } else if new_layout.size() > old_layout.size() {
            return Err(AllocError::ShrinkBiggerNewLayout(
                old_layout.size(),
                new_layout.size(),
            ));
        } else if new_layout.size() == old_layout.size() {
            return Ok(ptr);
        }
        null_q(
            ffi::raw_ralloc(ptr.as_ptr().cast(), old_layout, new_layout),
            new_layout,
        )
    }

    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.align() != old_layout.align() {
            return Err(AllocError::UnsupportedOperation(
                UOp::ReallocDifferentAlign(old_layout.align(), new_layout.align()),
            ));
        }
        null_q(
            ffi::raw_ralloc(ptr.as_ptr().cast(), old_layout, new_layout),
            new_layout,
        )
    }
}
