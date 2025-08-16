#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
use crate::{
    ffi::mim as ffi,
    helpers::{nonnull_to_void, null_q, null_q_zsl_check},
    Alloc, AllocError, Layout,
};
use core::ptr::NonNull;
use libc::c_void;

/// Handle to the `MiMalloc` allocator. This type implements the [`GlobalAlloc`] trait, allowing use
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

#[cfg(not(feature = "no_alloc"))]
unsafe impl alloc::alloc::GlobalAlloc for MiMalloc {
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
fn zsl_check_alloc<F: Fn(usize, usize) -> *mut c_void>(
    layout: Layout,
    alloc: F,
) -> Result<NonNull<u8>, AllocError> {
    #[cfg(feature = "mimalloc_err_reporting")]
    {
        match null_q_zsl_check(
            layout,
            |layout| alloc(layout.size(), layout.align()),
            null_q,
        ) {
            Err(AllocError::AllocFailed(l, _)) => {
                let code = LAST_ERR.load(core::sync::atomic::Ordering::SeqCst);
                Err(if code == 0 {
                    AllocError::AllocFailed(l, crate::error::Cause::Unknown)
                } else {
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
            |layout| alloc(layout.size(), layout.align()),
            null_q,
        )
    }
}

impl Alloc for MiMalloc {
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zsl_check_alloc(layout, |s, a| unsafe { ffi::mi_malloc_aligned(s, a) })
    }

    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        zsl_check_alloc(layout, |s, a| unsafe { ffi::mi_zalloc_aligned(s, a) })
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            ffi::mi_free_size_aligned(nonnull_to_void(ptr), layout.size(), layout.align());
        }
    }

    // TODO: dedup these

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        let old_size = old_layout.size();
        let new_size = new_layout.size();

        let new_align = new_layout.align();

        if new_size == old_size && new_align == old_layout.align() {
            return Ok(ptr);
        } else if new_size < old_size {
            return Err(AllocError::GrowSmallerNewLayout(old_size, new_size));
        }

        zsl_check_alloc(new_layout, |_, _| {
            ffi::mi_realloc_aligned(nonnull_to_void(ptr), new_size, new_align)
        })
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        let old_size = old_layout.size();
        let new_size = new_layout.size();

        let new_align = new_layout.align();

        if new_size == old_size && new_align == old_layout.align() {
            return Ok(ptr);
        } else if new_size > old_size {
            return Err(AllocError::ShrinkBiggerNewLayout(old_size, new_size));
        }

        zsl_check_alloc(new_layout, |_, _| {
            ffi::mi_realloc_aligned(nonnull_to_void(ptr), new_size, new_align)
        })
    }

    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        _: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        zsl_check_alloc(new_layout, |s, a| unsafe {
            ffi::mi_realloc_aligned(nonnull_to_void(ptr), s, a)
        })
    }
}

#[cfg(feature = "resize_in_place")]
pub(crate) const SHRINK_IP: AllocError =
    AllocError::Other("unsupported operation: attempted to shrink in place");

#[cfg(feature = "resize_in_place")]
impl crate::ResizeInPlace for MiMalloc {
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
            // this would be, though
            if ffi::mi_expand(ptr.as_ptr().cast::<c_void>(), new_size).is_null() {
                Err(crate::features::resize_in_place::CANNOT_RESIZE_IP)
            } else {
                Ok(())
            }
        }
    }

    // TODO: verify this is true
    /// Shrinking in-place is not supported by mimalloc.
    ///
    /// This is a noop and always returns an error.
    ///
    /// # Errors
    ///
    /// - [`AllocError::Other`]`("unsupported operation: attempted to shrink in place")`.
    // it just returns an error, no reason not to inline it.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    unsafe fn shrink_in_place(
        &self,
        _: NonNull<u8>,
        _: Layout,
        _: usize,
    ) -> Result<(), AllocError> {
        Err(SHRINK_IP)
    }
}

#[cfg(feature = "alloc_aligned_at")]
impl crate::features::alloc_aligned_at::AllocAlignedAt for MiMalloc {
    fn alloc_at(&self, layout: Layout, offset: usize) -> Result<(NonNull<u8>, Layout), AllocError> {
        zsl_check_alloc(layout, |s, a| unsafe {
            ffi::mi_malloc_aligned_at(s, a, offset)
        })
        .map(|ptr| (ptr, layout))
    }

    fn zalloc_at(
        &self,
        layout: Layout,
        offset: usize,
    ) -> Result<(NonNull<u8>, Layout), AllocError> {
        zsl_check_alloc(layout, |s, a| unsafe {
            ffi::mi_zalloc_aligned_at(s, a, offset)
        })
        .map(|ptr| (ptr, layout))
    }
}

#[cfg(feature = "fallible_dealloc")]
impl crate::features::fallible_dealloc::DeallocChecked for MiMalloc {
    fn status(
        &self,
        ptr: NonNull<u8>,
        layout: Layout,
    ) -> crate::features::fallible_dealloc::BlockStatus {
        use crate::features::fallible_dealloc::BlockStatus;

        let align = crate::features::fallible_dealloc::ptr_max_align(ptr);

        if self.owns(ptr) {
            if unsafe {
                ffi::mi_good_size(layout.size()) != ffi::mi_usable_size(nonnull_to_void(ptr))
            } {
                BlockStatus::OwnedIncomplete(None)
            } else if align < layout.align() {
                BlockStatus::OwnedMisaligned(Some(align))
            } else {
                BlockStatus::Owned
            }
        } else if align < layout.align() {
            BlockStatus::NotOwnedMisaligned(Some(align))
        } else {
            BlockStatus::NotOwned
        }
    }

    fn owns(&self, ptr: NonNull<u8>) -> bool {
        unsafe { ffi::mi_is_in_heap_region(nonnull_to_void(ptr)) }
    }
}
