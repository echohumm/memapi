// genuinely no clue how to doc these unsafe blocks
#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]

use {
    crate::{
        Alloc,
        Layout,
        error::AllocError,
        external::{fals, ffi::jem as ffi, no_err},
        helpers::{nonnull_to_void, null_q_dyn, null_q_zsl_check}
    },
    core::{ptr, ptr::NonNull},
    libc::c_void
};

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

unsafe fn resize_common(
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    zero_tail: bool,
    check_size: fn(&usize, &usize) -> bool,
    inv_size_err: fn(usize, usize) -> AllocError
) -> Result<NonNull<u8>, AllocError> {
    let old_size = old_layout.size();
    let new_size = new_layout.size();
    let new_align = new_layout.align();
    let old_align = old_layout.align();

    let same_align = old_align == new_align;

    if same_align && old_size == new_size {
        return Ok(ptr);
    } else if check_size(&old_size, &new_size) {
        return Err(inv_size_err(old_size, new_size));
    }

    let p = tri!(
        do null_q_dyn(raw_ralloc(ptr, old_layout, new_layout), new_layout)
    );
    if zero_tail && new_size > old_size {
        ptr::write_bytes(p.as_ptr().add(old_size), 0, new_size.saturating_sub(old_size));
    }

    dealloc(ptr.as_ptr(), old_layout);
    Ok(p)
}

/// Handle to the Jemalloc allocator. This type implements the [`GlobalAlloc`] trait, allowing use
/// as a global allocator, and [`Alloc`](Alloc).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Jemalloc;

fn alloc(layout: Layout) -> *mut c_void {
    unsafe {
        assume!(layout.size() != 0);

        let flags = ffi::layout_to_flags(layout.size(), layout.align());
        if flags == 0 { ffi::malloc(layout.size()) } else { ffi::mallocx(layout.size(), flags) }
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
        ffi::layout_to_flags(layout.size(), layout.align())
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
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 { alloc(layout).cast::<u8>() }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) { dealloc(ptr, layout); }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 { zalloc(layout).cast::<u8>() }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        assume!(!ptr.is_null());
        raw_ralloc(
            NonNull::new_unchecked(ptr),
            layout,
            Layout::from_size_align_unchecked(new_size, layout.align())
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
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        resize_common(
            ptr,
            old_layout,
            new_layout,
            false,
            core::cmp::PartialOrd::gt,
            AllocError::grow_smaller
        )
    }

    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        resize_common(
            ptr,
            old_layout,
            new_layout,
            true,
            core::cmp::PartialOrd::gt,
            AllocError::grow_smaller
        )
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        resize_common(
            ptr,
            old_layout,
            new_layout,
            false,
            core::cmp::PartialOrd::lt,
            AllocError::shrink_larger
        )
    }

    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        resize_common(ptr, old_layout, new_layout, false, fals, no_err)
    }

    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        resize_common(ptr, old_layout, new_layout, true, fals, no_err)
    }
}

#[cfg(feature = "resize_in_place")]
impl crate::ResizeInPlace for Jemalloc {
    unsafe fn grow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(crate::resize_in_place::RESIZE_IP_ZS)
        } else if new_size < old_layout.size() {
            Err(AllocError::grow_smaller(old_layout.size(), new_size))
        } else {
            // it isn't my fault if this is wrong lol
            if ffi::xallocx(
                ptr.as_ptr().cast::<c_void>(),
                new_size,
                0,
                ffi::layout_to_flags(new_size, old_layout.align())
            ) >= new_size
            {
                Ok(())
            } else {
                Err(crate::resize_in_place::CANNOT_RESIZE_IP)
            }
        }
    }

    unsafe fn shrink_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(crate::resize_in_place::RESIZE_IP_ZS)
        } else if new_size > old_layout.size() {
            Err(AllocError::shrink_larger(old_layout.size(), new_size))
        } else if new_size == old_layout.size() {
            // noop
            Ok(())
        } else {
            let flags = ffi::layout_to_flags(new_size, old_layout.align());
            let usable_size = ffi::xallocx(ptr.as_ptr().cast::<c_void>(), new_size, 0, flags);

            if usable_size < old_layout.size() {
                Ok(())
            } else if usable_size == ffi::nallocx(new_size, flags) {
                debug_assert_eq!(
                    crate::external::ffi::jem::nallocx(new_size, flags),
                    crate::external::ffi::jem::nallocx(old_layout.size(), flags)
                );

                Ok(())
            } else {
                // is this even possible?
                Err(crate::resize_in_place::CANNOT_RESIZE_IP)
            }
        }
    }
}
