#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
use {
    crate::{
        Alloc,
        AllocError,
        Layout,
        external::ffi::mim as ffi,
        helpers::{nonnull_to_void, null_q, null_q_zsl_check}
    },
    core::ptr::NonNull,
    libc::c_void
};

/// Handle to the `MiMalloc` allocator. This type implements the [`GlobalAlloc`] trait, allowing use
/// as a global allocator, and [`Alloc`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MiMalloc;

#[cfg(feature = "mimalloc_err_reporting")]
thread_local! {
    // 0 = ok, other = os error code
    static LAST_ERR: core::cell::Cell<i32> = core::cell::Cell::new(0);
}

#[cfg(feature = "mimalloc_global_err")]
static GLOBAL_LAST_ERR: core::sync::atomic::AtomicI32 = core::sync::atomic::AtomicI32::new(0);

#[cfg(feature = "mimalloc_global_err")]
/// Atomically loads the raw integer value of the last global error.
#[must_use]
pub fn get_global_last_err_val(ord: core::sync::atomic::Ordering) -> i32 {
    GLOBAL_LAST_ERR.load(ord)
}

#[cfg(feature = "mimalloc_global_err")]
/// Loads the last global error as an [`std::io::Error`] if present.
///
/// Returns `None` when the stored integer is `0`.
#[must_use]
pub fn get_global_last_err(ord: core::sync::atomic::Ordering) -> Option<std::io::Error> {
    match get_global_last_err_val(ord) {
        0 => None,
        v => Some(std::io::Error::from_raw_os_error(v))
    }
}

#[cfg(feature = "mimalloc_global_err")]
/// Clears the global error (sets it to `0`) using the given atomic ordering.
pub fn clear_global_last_err(ord: core::sync::atomic::Ordering) { GLOBAL_LAST_ERR.store(0, ord); }

#[cfg(feature = "mimalloc_global_err")]
/// Gets a static reference to the underlying atomic storing the last global error.
#[must_use]
pub fn global_err() -> &'static core::sync::atomic::AtomicI32 { &GLOBAL_LAST_ERR }

#[cfg(feature = "mimalloc_global_err")]
/// Copies the thread-local last error into the global error if possible.
///
/// If there's no thread-local error (`LAST_ERR == 0`) returns `Ok(false)`. If a thread-local error
/// exists and the global error was `0`, copies it into the global atomic, clears the thread-local
/// value *if `mov` is `true`*, and returns `Ok(true)`. Otherwise, returns an error.
///
/// `succ` is used as the success ordering for the underlying atomic compare-exchange, while `fail`
/// is used as the failure ordering.
///
/// # Errors
///
/// If a thread-local error exists but the global atomic was already non-zero,
/// returns`Err(current_global_value)`.
pub fn local_to_global_err(
    succ: core::sync::atomic::Ordering,
    fail: core::sync::atomic::Ordering,
    mov: bool
) -> Result<bool, i32> {
    let local = LAST_ERR.with(core::cell::Cell::get);
    if local == 0 {
        return Ok(false);
    }

    match GLOBAL_LAST_ERR.compare_exchange(0, local, succ, fail) {
        Ok(_) => {
            if mov {
                LAST_ERR.with(|c| c.set(0));
            }
            Ok(true)
        }
        Err(current_global) => Err(current_global)
    }
}

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
    LAST_ERR.with(|c| c.set(e));
}

#[cfg(all(feature = "mimalloc_err_reporting", not(feature = "mimalloc_err_output")))]
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
    alloc: F
) -> Result<NonNull<u8>, AllocError> {
    #[cfg(feature = "mimalloc_err_reporting")]
    {
        match null_q_zsl_check(layout, |layout| alloc(layout.size(), layout.align()), null_q) {
            Err(AllocError::AllocFailed(l, _)) => {
                let code = LAST_ERR.with(|c| {
                    let v = c.get();
                    if v != 0 {
                        c.set(0);
                    }
                    v
                });

                Err(if code == 0 {
                    AllocError::AllocFailed(l, crate::error::Cause::Unknown)
                } else {
                    AllocError::AllocFailed(
                        l,
                        crate::error::Cause::OSErr(std::io::Error::from_raw_os_error(code))
                    )
                })
            }
            Err(e) => Err(e),
            Ok(ptr) => Ok(ptr)
        }
    }

    #[cfg(not(feature = "mimalloc_err_reporting"))]
    {
        null_q_zsl_check(layout, |layout| alloc(layout.size(), layout.align()), null_q)
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

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        realloc(ptr, old_layout, new_layout, |old, new| {
            if new < old { Some(AllocError::grow_smaller(old, new)) } else { None }
        })
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        realloc(ptr, old_layout, new_layout, |old, new| {
            if new > old { Some(AllocError::shrink_larger(old, new)) } else { None }
        })
    }

    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        _: Layout,
        new_layout: Layout
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
        new_size: usize
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(crate::resize_in_place::RESIZE_IP_ZS)
        } else if new_size < old_layout.size() {
            Err(AllocError::grow_smaller(old_layout.size(), new_size))
        } else {
            // this would be, though
            if ffi::mi_expand(ptr.as_ptr().cast::<c_void>(), new_size).is_null() {
                Err(crate::resize_in_place::CANNOT_RESIZE_IP)
            } else {
                Ok(())
            }
        }
    }

    /// Shrinking in-place isn't supported by mimalloc.
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
        _: usize
    ) -> Result<(), AllocError> {
        Err(SHRINK_IP)
    }
}

#[cfg(feature = "alloc_aligned_at")]
impl crate::alloc_aligned_at::AllocAlignedAt for MiMalloc {
    fn alloc_at(&self, layout: Layout, offset: usize) -> Result<(NonNull<u8>, Layout), AllocError> {
        zsl_check_alloc(layout, |s, a| unsafe { ffi::mi_malloc_aligned_at(s, a, offset) })
            .map(|ptr| (ptr, layout))
    }

    fn zalloc_at(
        &self,
        layout: Layout,
        offset: usize
    ) -> Result<(NonNull<u8>, Layout), AllocError> {
        zsl_check_alloc(layout, |s, a| unsafe { ffi::mi_zalloc_aligned_at(s, a, offset) })
            .map(|ptr| (ptr, layout))
    }
}

#[cfg(feature = "checked_dealloc")]
impl crate::checked_dealloc::CheckedDealloc for MiMalloc {
    fn status(
        &self,
        ptr: NonNull<u8>,
        layout: Layout
    ) -> crate::checked_dealloc::BlockStatus {
        use crate::checked_dealloc::BlockStatus;

        let align = crate::helpers::ptr_max_align(ptr);

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

unsafe fn realloc(
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    size_err: impl Fn(usize, usize) -> Option<AllocError>
) -> Result<NonNull<u8>, AllocError> {
    let old_size = old_layout.size();
    let new_size = new_layout.size();
    let new_align = new_layout.align();

    if new_size == old_size && new_align == old_layout.align() {
        return Ok(ptr);
    } else if let Some(err) = size_err(old_size, new_size) {
        return Err(err);
    }

    zsl_check_alloc(new_layout, |_, _| {
        ffi::mi_realloc_aligned(nonnull_to_void(ptr), new_size, new_align)
    })
}
