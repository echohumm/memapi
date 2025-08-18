use {
    crate::{
        error::{AllocError, ArithOp},
        fallible_dealloc::DeallocChecked,
        helpers::checked_op,
        type_props::SizedProps
    },
    core::ptr::NonNull
};

/// Slice-specific extension methods for [`DeallocChecked`].
#[allow(clippy::module_name_repetitions)]
pub trait DeallocCheckedSlice: DeallocChecked {
    /// Attempts to deallocate a previously allocated block.
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](super::BlockStatus), or if the provided layout is zero-sized.
    #[cfg_attr(miri, track_caller)]
    fn try_dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) -> Result<(), AllocError> {
        let sz = tri!(AllocError::ArithmeticOverflow(checked_op(T::SZ, ArithOp::Mul, n)));
        self.try_dealloc(ptr.cast::<u8>(), tri!(lay, sz, T::ALN))
    }
}

impl<A: DeallocChecked + ?Sized> DeallocCheckedSlice for A {}
