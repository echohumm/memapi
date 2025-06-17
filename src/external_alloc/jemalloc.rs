use crate::external_alloc::ffi::jem::{self as ffi, layout_to_flags};
use core::alloc::{GlobalAlloc, Layout};

macro_rules! assume {
    ($e:expr) => {
        debug_assert!($e);
        if !($e) {
            core::hint::unreachable_unchecked();
        }
    };
}

/// Handle to the jemalloc allocator. This type implements the [`GlobalAlloc`] trait, allowing use as
/// a global allocator, and [`Alloc`](crate::Alloc).
#[derive(Copy, Clone, Default, Debug)]
pub struct Jemalloc;

unsafe impl GlobalAlloc for Jemalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        let flags = layout_to_flags(layout.size(), layout.align());
        let ptr = if flags == 0 {
            ffi::malloc(layout.size())
        } else {
            ffi::mallocx(layout.size(), flags)
        };
        ptr.cast()
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        assume!(!ptr.is_null());
        assume!(layout.size() != 0);
        let flags = layout_to_flags(layout.size(), layout.align());
        ffi::sdallocx(ptr.cast(), layout.size(), flags);
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        let flags = layout_to_flags(layout.size(), layout.align());
        let ptr = if flags == 0 {
            ffi::calloc(1, layout.size())
        } else {
            ffi::mallocx(layout.size(), flags | ffi::MALLOCX_ZERO)
        };
        ptr.cast()
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        assume!(layout.size() != 0);
        assume!(new_size != 0);
        let flags = layout_to_flags(new_size, layout.align());
        let ptr = if flags == 0 {
            ffi::realloc(ptr.cast(), new_size)
        } else {
            ffi::rallocx(ptr.cast(), new_size, flags)
        };
        ptr.cast()
    }
}
