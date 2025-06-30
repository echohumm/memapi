use crate::AllocError;
use alloc::alloc::Layout;
use core::fmt::{self, Display, Formatter};

#[cfg(feature = "metadata")]
/// Alternative to `*mut T`'s `with_metadata_of`, because it's unstable.
#[inline]
#[must_use = "this returns a new pointer"]
pub const fn with_meta<T: ?Sized, U: ?Sized>(ptr: *mut T, meta: *const U) -> *mut U {
    core::ptr::from_raw_parts_mut(ptr.cast::<()>(), core::ptr::metadata(meta))
}

#[cfg(feature = "metadata")]
/// Alternative to `*mut T`'s `with_metadata_of`, because it's unstable.
#[inline]
#[must_use = "this returns a new pointer"]
pub const fn with_meta_const<T: ?Sized, U: ?Sized>(ptr: *const T, meta: *const U) -> *const U {
    core::ptr::from_raw_parts(ptr.cast::<()>(), core::ptr::metadata(meta))
}

/// Alternative to [`Layout::padding_needed_for`], because it's unstable.
#[inline]
#[must_use]
pub const fn pad_layout_for(layout: Layout, align: usize) -> usize {
    if !align.is_power_of_two() {
        return usize::MAX;
    }

    unsafe {
        let sz = layout.size();
        size_rounded_up_to_align(sz, align).unchecked_sub(sz)
    }
}

/// Creates a layout by rounding the size of this layout up to a multiple of the layout's alignment.
///
/// This is equivalent to adding the result of [`pad_layout_for`] to the layout's current size.
#[inline]
#[must_use]
pub const fn pad_layout_to_align(layout: Layout, align: usize) -> Layout {
    unsafe {
        Layout::from_size_align_unchecked(
            size_rounded_up_to_align(layout.size(), align),
            layout.align(),
        )
    }
}

/// Creates a layout describing the record for `n` instances of `self`, with a suitable amount of
/// padding between each to ensure that each instance is given its requested size and alignment.
/// On success, returns `(k, offs)` where `k` is the layout of the array and `offs` is the distance
/// between the start of each element in the array.
///
/// (That distance between elements is sometimes known as "stride".)
///
/// # Errors
///
/// - [`AllocError::LayoutError`] if the computed layout is invalid.
/// - [`AllocError::ArithmeticOverflow`] if an arithmetic operation overflows.
#[inline]
pub const fn repeat_layout(
    layout: Layout,
    count: usize,
) -> Result<(Layout, usize), AllocError<UUError>> {
    let padded = pad_layout_to_align(layout, layout.align());
    match repeat_layout_packed(padded, count) {
        Ok(repeated) => Ok((repeated, padded.size())),
        Err(e) => Err(e),
    }
}

/// Creates a layout describing the record for `n` instances of
/// `self`, with no padding between each instance.
///
/// Note that, unlike [`repeat_layout`], `repeat_packed` does not guarantee that the repeated
/// instances of `self` will be properly aligned, even if a given instance of `self` is properly
/// aligned. In other words, if the layout returned by`repeat_packed` is used to allocate an array,
/// it is not guaranteed that all elements in the array will be properly aligned.
///
/// # Errors
///
/// - [`AllocError::LayoutError`] if the computed layout is invalid.
/// - [`AllocError::ArithmeticOverflow`] if an arithmetic operation overflows.
#[inline]
pub const fn repeat_layout_packed(
    layout: Layout,
    count: usize,
) -> Result<Layout, AllocError<UUError>> {
    if let Some(size) = layout.size().checked_mul(count) {
        let align = layout.align();
        match Layout::from_size_align(size, align) {
            Ok(layout) => Ok(layout),
            Err(_) => Err(AllocError::LayoutError(layout.size(), layout.align())),
        }
    } else {
        Err(AllocError::Other(UUError::ArithmeticOverflow))
    }
}

const fn size_rounded_up_to_align(sz: usize, align: usize) -> usize {
    unsafe {
        let sub1 = align.unchecked_sub(1);
        sz.unchecked_add(sub1) & !sub1
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
/// An error which can occur specifically when using [`unstable_util`](crate::unstable_util).
pub enum UUError {
    /// A basic arithmetic operation overflowed.
    ArithmeticOverflow,
}

impl Display for UUError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            UUError::ArithmeticOverflow => write!(f, "arithmetic overflow"),
        }
    }
}

impl core::error::Error for UUError {}
