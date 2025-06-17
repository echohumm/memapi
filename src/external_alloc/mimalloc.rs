use crate::ffi;
use core::alloc::{GlobalAlloc, Layout};

macro_rules! assume {
    ($e:expr) => {
        debug_assert!($e);
        if !($e) {
            core::hint::unreachable_unchecked()
        }
    };
}

/// Handle to the mimalloc allocator. This type implements the [`GlobalAlloc`] trait, allowing use as
/// a global allocator, and [`Alloc`](crate::Alloc).
pub struct MiMalloc;

unsafe impl GlobalAlloc for MiMalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        ffi::mim::mi_malloc_aligned(layout.size(), layout.align()).cast()
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, _: Layout) {
        assume!(!ptr.is_null());
        ffi::mim::mi_free(ptr.cast());
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        assume!(layout.size() != 0);
        ffi::mim::mi_zalloc_aligned(layout.size(), layout.align()).cast()
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        assume!(layout.size() != 0);
        assume!(new_size != 0);
        ffi::mim::mi_realloc_aligned(ptr.cast(), new_size, layout.align()).cast()
    }
}
