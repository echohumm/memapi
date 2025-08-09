use crate::{
    error::{AllocError, ArithOp, LayoutErr},
    helpers::align_up_unchecked,
    type_props::USIZE_MAX_NO_HIGH_BIT,
};
use alloc::alloc::Layout;

#[cfg(feature = "metadata")]
/// Alternative to `*mut T`'s `with_metadata_of`, because it's unstable.
#[must_use = "this returns a new pointer"]
pub const fn with_meta<T: ?Sized, U: ?Sized>(ptr: *mut T, meta: *const U) -> *mut U {
    core::ptr::from_raw_parts_mut(ptr.cast::<()>(), core::ptr::metadata(meta))
}

#[cfg(feature = "metadata")]
/// Alternative to `*mut T`'s `with_metadata_of`, because it's unstable.
#[must_use = "this returns a new pointer"]
pub const fn with_meta_const<T: ?Sized, U: ?Sized>(ptr: *const T, meta: *const U) -> *const U {
    core::ptr::from_raw_parts(ptr.cast::<()>(), core::ptr::metadata(meta))
}

/// Alternative to [`Layout::padding_needed_for`], because it's unstable.
#[must_use]
#[inline]
pub const fn pad_layout_for(layout: Layout, align: usize) -> usize {
    if !align.is_power_of_two() {
        return usize::MAX;
    }

    let sz = layout.size();
    unsafe { align_up_unchecked(sz, align) - sz }
}

/// Creates a layout by rounding the size of this layout up to a multiple of the layout's alignment.
///
/// This is equivalent to adding the result of [`pad_layout_for`] to the layout's current size.
#[must_use]
#[inline]
pub const fn pad_layout_to_align(layout: Layout, align: usize) -> Layout {
    if !align.is_power_of_two() {
        return unsafe { Layout::from_size_align_unchecked(USIZE_MAX_NO_HIGH_BIT, 1) };
    }

    unsafe {
        Layout::from_size_align_unchecked(align_up_unchecked(layout.size(), align), layout.align())
    }
}

// TODO: make these const

#[cfg(not(feature = "os_err_reporting"))]
/// Creates a layout describing the record for `n` instances of `self`, with a suitable amount of
/// padding between each to ensure that each instance is given its requested size and alignment.
/// On success, returns `(k, offs)` where `k` is the layout of the array and `offs` is the distance
/// between the start of each element in the array.
///
/// (That distance between elements is sometimes known as "stride".)
///
/// # Errors
///
/// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
/// - [`AllocError::Other`]`("arithmetic operation overflowed")` if an arithmetic operation
///   overflows.
#[inline]
pub const fn repeat_layout(layout: Layout, count: usize) -> Result<(Layout, usize), AllocError> {
    let padded = pad_layout_to_align(layout, layout.align());
    match repeat_layout_packed(padded, count) {
        Ok(repeated) => Ok((repeated, padded.size())),
        Err(e) => Err(e),
    }
}

#[cfg(feature = "os_err_reporting")]
/// Creates a layout describing the record for `n` instances of `self`, with a suitable amount of
/// padding between each to ensure that each instance is given its requested size and alignment.
/// On success, returns `(k, offs)` where `k` is the layout of the array and `offs` is the distance
/// between the start of each element in the array.
///
/// (That distance between elements is sometimes known as "stride".)
///
/// # Errors
///
/// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
/// - [`AllocError::Other`]`("arithmetic operation overflowed")` if an arithmetic operation
///   overflows.
///
/// This method is not `const` as `os_err_reporting` is enabled.
#[inline]
pub fn repeat_layout(layout: Layout, count: usize) -> Result<(Layout, usize), AllocError> {
    let padded = pad_layout_to_align(layout, layout.align());
    match repeat_layout_packed(padded, count) {
        Ok(repeated) => Ok((repeated, padded.size())),
        Err(e) => Err(e),
    }
}

/// Creates a layout describing the record for `n` instances of
/// `self`, with no padding between each instance.
///
/// Note that, unlike [`repeat_layout`], `repeat_packed` doesn't guarantee that the repeated
/// instances of `self` will be properly aligned, even if a given instance of `self` is properly
/// aligned. In other words, if the layout returned by`repeat_packed` is used to allocate an array,
/// it isn't guaranteed that all elements in the array will be properly aligned.
///
/// # Errors
///
/// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
/// - [`AllocError::ArithmeticOverflow`] if an arithmetic operation overflows.
#[inline]
pub const fn repeat_layout_packed(layout: Layout, count: usize) -> Result<Layout, AllocError> {
    #[allow(clippy::option_if_let_else)]
    // TODO: use checked_op function
    if let Some(size) = { layout.size().checked_mul(count) } {
        let align = layout.align();
        match layout_from_size_align(size, align) {
            Ok(layout) => Ok(layout),
            Err(r) => Err(AllocError::InvalidLayout(layout.size(), layout.align(), r)),
        }
    } else {
        Err(AllocError::ArithmeticOverflow(
            layout.size(),
            ArithOp::Mul,
            count,
        ))
    }
}

const fn layout_from_size_align(sz: usize, aln: usize) -> Result<Layout, LayoutErr> {
    if aln == 0 {
        return Err(LayoutErr::ZeroAlign);
    } else if !aln.is_power_of_two() {
        return Err(LayoutErr::NonPowerOfTwoAlign);
    } else if sz > USIZE_MAX_NO_HIGH_BIT + 1 - aln {
        return Err(LayoutErr::Overflow);
    }

    Ok(unsafe { Layout::from_size_align_unchecked(sz, aln) })
}
