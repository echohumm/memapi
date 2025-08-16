use crate::{
    base_try_dealloc_impl, error::AllocError, type_props::PtrProps, DeallocChecked, Layout,
};
use core::ptr::{self, NonNull};

// this file seems to be a cognitohazard

/// Extension methods for [`DeallocChecked`]
#[allow(clippy::module_name_repetitions)]
pub trait DeallocCheckedExt: DeallocChecked {
    /// Attempts to drop the data at a pointer and deallocate its previously allocated block.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - be properly aligned
    /// - point to a valid `T`
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[track_caller]
    #[inline]
    unsafe fn try_drop_and_dealloc<T: ?Sized>(&self, ptr: NonNull<T>) -> Result<(), AllocError> {
        base_try_dealloc_impl(self, ptr, ptr.layout(), |d, ptr, layout| {
            ptr::drop_in_place(ptr.as_ptr());
            d.dealloc(ptr.cast::<u8>(), layout);
        })
    }

    /// Attempts to zero and deallocate the memory at a pointer.
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn try_zero_and_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), AllocError> {
        // SAFETY: ptr was allocated by us with the given layout
        base_try_dealloc_impl(self, ptr, layout, |d, ptr, layout| unsafe {
            let p = ptr.cast();
            ptr::write_bytes(p.as_ptr(), 0, layout.size());
            d.dealloc(p, layout);
        })
    }

    /// Deallocates a pointer's memory.
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn try_dealloc_typed<T: ?Sized>(&self, ptr: NonNull<T>) -> Result<(), AllocError> {
        // SAFETY: even if the layout from the pointer is invalid because the pointer is, we check
        //  later.
        self.try_dealloc(ptr.cast::<u8>(), unsafe { ptr.layout() })
    }

    /// Zeroes and deallocates the memory at a pointer.
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn try_zero_and_dealloc_typed<T: ?Sized>(&self, ptr: NonNull<T>) -> Result<(), AllocError> {
        // SAFETY: see try_dealloc_typed
        self.try_zero_and_dealloc(ptr.cast::<u8>(), unsafe { ptr.layout() })
    }

    /// Drops the value at the given pointer, then zeroes and deallocates its memory.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - be properly aligned
    /// - point to a valid `T`
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[track_caller]
    #[inline]
    unsafe fn drop_zero_and_dealloc<T: ?Sized>(&self, ptr: NonNull<T>) -> Result<(), AllocError> {
        base_try_dealloc_impl(self, ptr, ptr.layout(), |d, ptr, layout| {
            ptr::drop_in_place(ptr.as_ptr());
            let p = ptr.cast();
            ptr::write_bytes(p.as_ptr(), 0, layout.size());
            d.dealloc(p, layout);
        })
    }
}

impl<D: DeallocChecked + ?Sized> DeallocCheckedExt for D {}
