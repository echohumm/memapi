use crate::fallible_dealloc::{base_try_dealloc_impl, DeallocChecked};
use crate::{
    error::{AllocError, ArithOp},
    helpers::{checked_op, nonnull_slice_len, slice_ptr_from_raw_parts},
    type_props::SizedProps,
};
use core::{
    mem::MaybeUninit,
    ptr::{self, NonNull},
};

/// Slice-specific extension methods for [`DeallocChecked`].
#[allow(clippy::module_name_repetitions)]
pub trait DeallocCheckedSlice: DeallocChecked {
    /// Attempts to zero and deallocate `n` elements at the given pointer.
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[cfg_attr(miri, track_caller)]
    fn try_zero_and_dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) -> Result<(), AllocError> {
        let sz = tri!(AllocError::ArithmeticOverflow(checked_op(
            T::SZ,
            ArithOp::Mul,
            n
        )));
        base_try_dealloc_impl(
            self,
            ptr,
            tri!(lay, sz, T::ALN),
            // SAFETY: ptr was allocated by us with the given layout
            |d, ptr, layout| unsafe {
                let p_bytes = ptr.cast::<u8>();
                ptr::write_bytes(p_bytes.as_ptr(), 0, layout.size());
                d.dealloc(p_bytes, layout);
            },
        )
    }

    /// Attempts to deallocate a previously allocated block.
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[cfg_attr(miri, track_caller)]
    fn try_dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) -> Result<(), AllocError> {
        let sz = tri!(AllocError::ArithmeticOverflow(checked_op(
            T::SZ,
            ArithOp::Mul,
            n
        )));
        self.try_dealloc(ptr.cast::<u8>(), tri!(lay, sz, T::ALN))
    }
}

impl<A: DeallocChecked + ?Sized> DeallocCheckedSlice for A {}

#[cfg(feature = "alloc_ext")]
/// Higher-level slice-specific extension methods for [`DeallocChecked`].
pub trait DeallocCheckedSliceExt: DeallocCheckedSlice {
    /// Attempts to drop `init` elements from a partially initialized slice, then zero and
    /// deallocate its memory.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - be properly aligned
    /// - point to `init` valid `T`
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[track_caller]
    unsafe fn try_drop_zero_and_dealloc_uninit_slice<T>(
        &self,
        slice: NonNull<[MaybeUninit<T>]>,
        init: usize,
    ) -> Result<(), AllocError> {
        self.try_drop_zero_and_dealloc_raw_slice(slice.cast::<T>(), init, nonnull_slice_len(slice))
    }

    /// Attempts to drop `init` elements from a pointer to a slice, then zeroes and deallocates its
    /// previously allocated block.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - be properly aligned
    /// - point to `init` valid `T`
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[track_caller]
    unsafe fn try_drop_zero_and_dealloc_raw_slice<T>(
        &self,
        slice: NonNull<T>,
        init: usize,
        len: usize,
    ) -> Result<(), AllocError> {
        let sz = tri!(AllocError::ArithmeticOverflow(checked_op(
            T::SZ,
            ArithOp::Mul,
            len
        )));
        base_try_dealloc_impl(self, slice, tri!(lay, sz, T::ALN), |d, ptr, layout| {
            ptr::drop_in_place(slice_ptr_from_raw_parts(ptr.as_ptr(), init));
            let p_bytes = ptr.cast::<u8>();
            ptr::write_bytes(p_bytes.as_ptr(), 0, layout.size());
            d.dealloc(p_bytes, layout);
        })
    }

    /// Attempts to drop `init` elements from a partially initialized slice and deallocate it.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - be properly aligned
    /// - point to `init` valid `T`
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[cfg_attr(miri, track_caller)]
    unsafe fn try_drop_and_dealloc_uninit_slice<T>(
        &self,
        ptr: NonNull<[MaybeUninit<T>]>,
        init: usize,
    ) -> Result<(), AllocError> {
        let len = nonnull_slice_len(ptr);
        self.try_drop_and_dealloc_raw_slice(ptr.cast::<T>(), init, len)
    }

    /// Attempts to drop `init` elements from a pointer to a slice and deallocate its previously
    /// allocated block.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - be properly aligned
    /// - point to `init` valid `T`
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[track_caller]
    unsafe fn try_drop_and_dealloc_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        init: usize,
        len: usize,
    ) -> Result<(), AllocError> {
        let sz = tri!(AllocError::ArithmeticOverflow(checked_op(
            T::SZ,
            ArithOp::Mul,
            len
        )));
        base_try_dealloc_impl(self, ptr, tri!(lay, sz, T::ALN), |d, ptr, layout| {
            ptr::drop_in_place(slice_ptr_from_raw_parts(ptr.as_ptr(), init));
            d.dealloc(ptr.cast::<u8>(), layout);
        })
    }
}

#[cfg(feature = "alloc_ext")]
impl<A: DeallocCheckedSlice + ?Sized> DeallocCheckedSliceExt for A {}
