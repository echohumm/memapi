#![allow(clippy::undocumented_unsafe_blocks)]
use crate::{
    external_alloc::resize,
    ffi::mim as ffi,
    helpers::{null_q, null_q_zsl_check},
    Alloc, AllocError,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::NonNull,
};
use libc::c_void;

/// Handle to the mimalloc allocator. This type implements the [`GlobalAlloc`] trait, allowing use
/// as a global allocator, and [`Alloc`].
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MiMalloc;

#[cfg(feature = "mimalloc_err_reporting")]
// 0 = ok
// others = os error code
static LAST_ERR: core::sync::atomic::AtomicI32 = core::sync::atomic::AtomicI32::new(0);

#[cfg(feature = "mimalloc_err_reporting")]
/// Initializes the `MiMalloc` error/output handler.
///
/// This should only be called once, before any allocations.
pub fn init_error_handler() {
    unsafe {
        #[cfg(not(feature = "mimalloc_err_output"))]
        ffi::mi_register_output(Some(discard_output), core::ptr::null_mut());
        ffi::mi_register_error(Some(error_handler), core::ptr::null_mut());
    }
}

#[cfg(feature = "mimalloc_err_reporting")]
#[no_mangle]
unsafe extern "C" fn error_handler(e: libc::c_int, _: *mut c_void) {
    #[cfg(feature = "mim_secure")]
    if e == libc::EFAULT {
        libc::abort();
    }
    LAST_ERR.store(e, core::sync::atomic::Ordering::SeqCst);
}

#[cfg(all(
    feature = "mimalloc_err_reporting",
    not(feature = "mimalloc_err_output")
))]
#[no_mangle]
unsafe extern "C" fn discard_output(_: *const libc::c_char, _: *mut c_void) {}

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
    #[cfg(feature = "mimalloc_err_reporting")]
    {
        match null_q_zsl_check(
            layout,
            |layout| unsafe { alloc(layout.size(), layout.align()) },
            null_q,
        ) {
            Err(AllocError::AllocFailed(l, _)) => {
                let code = LAST_ERR.load(core::sync::atomic::Ordering::SeqCst);
                Err(if code != 0 {
                    // only reset if it hasn't been updated already
                    let _ = LAST_ERR.compare_exchange(
                        code,
                        0,
                        core::sync::atomic::Ordering::SeqCst,
                        core::sync::atomic::Ordering::SeqCst,
                    );
                    AllocError::AllocFailed(
                        l,
                        crate::error::Cause::OSErr(std::io::Error::from_raw_os_error(code)),
                    )
                } else {
                    AllocError::AllocFailed(l, crate::error::Cause::Unknown)
                })
            }
            Err(e) => Err(e),
            Ok(ptr) => Ok(ptr),
        }
    }

    #[cfg(not(feature = "mimalloc_err_reporting"))]
    {
        null_q_zsl_check(
            layout,
            |layout| unsafe { alloc(layout.size(), layout.align()) },
            null_q,
        )
    }
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
        // TODO: make this able to return an error if the pointer is not allocated by this allocator
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
        null_q_zsl_check(
            new_layout,
            |new_layout| {
                ffi::mi_realloc_aligned(
                    ptr.as_ptr().cast::<c_void>(),
                    new_layout.size(),
                    new_layout.align(),
                )
            },
            null_q,
        )
    }
}
