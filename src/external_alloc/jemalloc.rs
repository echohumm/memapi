// genuinely no clue how to doc these unsafe blocks
#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
use crate::{
    error::AllocError,
    external_alloc::ffi::jem as ffi,
    helpers::{nonnull_to_void, null_q_dyn, null_q_zsl_check},
    Alloc, Layout,
};
use core::ptr::NonNull;
use libc::c_void;

macro_rules! assume {
    ($e:expr) => {
        #[cfg(debug_assertions)]
        {
            assert!($e, concat!("assertion failed: ", stringify!($e)));
        }
        if !($e) {
            core::hint::unreachable_unchecked();
        }
    };
}

unsafe fn resize<F: Fn() -> *mut c_void>(
    ralloc: F,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    is_grow: bool,
    nq: fn(*mut c_void, Layout) -> Result<NonNull<u8>, AllocError>,
) -> Result<NonNull<u8>, AllocError> {
    let new_align = new_layout.align();
    let old_align = old_layout.align();

    let old_size = old_layout.size();
    let new_size = new_layout.size();

    if new_size == old_size && new_align == old_align {
        return Ok(ptr);
    } else if is_grow {
        if new_size < old_size {
            return Err(AllocError::GrowSmallerNewLayout(old_size, new_size));
        }
    } else if new_size > old_size {
        return Err(AllocError::ShrinkBiggerNewLayout(old_size, new_size));
    }

    nq(ralloc(), new_layout)
}

/// Handle to the Jemalloc allocator. This type implements the [`GlobalAlloc`] trait, allowing use
/// as a global allocator, and [`Alloc`](Alloc).
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Jemalloc;

fn alloc(layout: Layout) -> *mut c_void {
    unsafe {
        assume!(layout.size() != 0);
    }
    let flags = ffi::layout_to_flags(layout.size(), layout.align());
    if flags == 0 {
        unsafe { ffi::malloc(layout.size()) }
    } else {
        unsafe { ffi::mallocx(layout.size(), flags) }
    }
}

fn zalloc(layout: Layout) -> *mut c_void {
    unsafe {
        assume!(layout.size() != 0);
    }
    let flags = ffi::layout_to_flags(layout.size(), layout.align());
    if flags == 0 {
        unsafe { ffi::calloc(1, layout.size()) }
    } else {
        unsafe { ffi::mallocx(layout.size(), flags | ffi::MALLOCX_ZERO) }
    }
}

unsafe fn dealloc(ptr: *mut u8, layout: Layout) {
    assume!(!ptr.is_null());
    assume!(layout.size() != 0);
    ffi::sdallocx(
        ptr.cast::<c_void>(),
        layout.size(),
        ffi::layout_to_flags(layout.size(), layout.align()),
    );
}

unsafe fn raw_ralloc(ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> *mut c_void {
    assume!(old_layout.size() != 0);
    assume!(new_layout.size() != 0);
    let flags = ffi::layout_to_flags(new_layout.size(), old_layout.align());
    if flags == 0 {
        ffi::realloc(nonnull_to_void(ptr), new_layout.size())
    } else {
        ffi::rallocx(nonnull_to_void(ptr), new_layout.size(), flags)
    }
}

#[cfg(not(feature = "no_alloc"))]
unsafe impl alloc::alloc::GlobalAlloc for Jemalloc {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        alloc(layout).cast::<u8>()
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        dealloc(ptr, layout);
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        zalloc(layout).cast::<u8>()
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        assume!(!ptr.is_null());
        raw_ralloc(
            NonNull::new_unchecked(ptr),
            layout,
            Layout::from_size_align_unchecked(new_size, layout.align()),
        )
        .cast::<u8>()
    }
}

impl Alloc for Jemalloc {
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        null_q_zsl_check(layout, alloc, null_q_dyn)
    }

    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        null_q_zsl_check(layout, zalloc, null_q_dyn)
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
            || raw_ralloc(ptr, old_layout, new_layout),
            ptr,
            old_layout,
            new_layout,
            true,
            null_q_dyn,
        )
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        resize(
            || raw_ralloc(ptr, old_layout, new_layout),
            ptr,
            old_layout,
            new_layout,
            false,
            null_q_dyn,
        )
    }

    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        null_q_dyn(raw_ralloc(ptr, old_layout, new_layout), new_layout)
    }
}

#[cfg(feature = "resize_in_place")]
impl crate::ResizeInPlace for Jemalloc {
    unsafe fn grow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(crate::features::resize_in_place::RESIZE_IP_ZS)
        } else if new_size < old_layout.size() {
            Err(AllocError::GrowSmallerNewLayout(
                old_layout.size(),
                new_size,
            ))
        } else {
            // it isn't my fault if this is wrong lol
            if ffi::xallocx(
                ptr.as_ptr().cast::<c_void>(),
                new_size,
                0,
                ffi::layout_to_flags(new_size, old_layout.align()),
            ) >= new_size
            {
                Ok(())
            } else {
                Err(crate::features::resize_in_place::CANNOT_RESIZE_IP)
            }
        }
    }

    unsafe fn shrink_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(crate::features::resize_in_place::RESIZE_IP_ZS)
        } else if new_size > old_layout.size() {
            Err(AllocError::ShrinkBiggerNewLayout(
                old_layout.size(),
                new_size,
            ))
        } else if new_size == old_layout.size() {
            // noop
            Ok(())
        } else {
            let flags = ffi::layout_to_flags(new_size, old_layout.align());
            let usable_size = ffi::xallocx(ptr.as_ptr().cast::<libc::c_void>(), new_size, 0, flags);

            if usable_size < old_layout.size() {
                Ok(())
            } else if usable_size == ffi::nallocx(new_size, flags) {
                debug_assert_eq!(
                    crate::external_alloc::ffi::jem::nallocx(new_size, flags),
                    crate::external_alloc::ffi::jem::nallocx(old_layout.size(), flags)
                );

                Ok(())
            } else {
                // is this even possible?
                Err(crate::features::resize_in_place::CANNOT_RESIZE_IP)
            }
        }
    }
}
