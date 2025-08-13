use crate::{
    error::{
        ArithOp,
        InvLayout,
        LayoutErr,
        RepeatLayoutError,
        AlignErr
    },
    helpers::{align_up_unchecked, checked_op},
    type_props::USIZE_HIGH_BIT
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
pub const fn layout_padding_for(layout: Layout, align: usize) -> usize {
    if !align.is_power_of_two() {
        return usize::MAX;
    }

    let sz = layout.size();
    // SAFETY: we just checked that the alignment was valid
    unsafe { align_up_unchecked(sz, align) - sz }
}

/// Creates a layout by rounding the size of this layout up to a multiple of the layout's alignment.
///
/// This is equivalent to adding the result of [`layout_padding_for`] to the layout's current size.
#[must_use]
#[inline]
pub const fn pad_layout_to_align(layout: Layout) -> Layout {
    // SAFETY: layout's requirements guarantee that the rounded up size is valid.
    unsafe {
        Layout::from_size_align_unchecked(
            align_up_unchecked(layout.size(), layout.align()),
            layout.align(),
        )
    }
}

/// Creates a layout for `n` instances of the value described by `layout`, with padding between each
/// to ensure that each instance is given its requested size and alignment.
///
/// On success, returns `(l, offs)` where `l` is the layout of the array and `offs` is the distance
/// between the start of each element in the array (stride).
///
/// # Errors
///
/// - [`RepeatLayoutError::InvalidLayout`] if the computed layout is invalid.
/// - [`RepeatLayoutError::ArithmeticOverflow`] if an arithmetic operation
///   would overflow.
#[inline]
pub const fn repeat_layout(
    layout: Layout,
    count: usize,
) -> Result<(Layout, usize), RepeatLayoutError> {
    let padded = pad_layout_to_align(layout);
    match repeat_layout_packed(padded, count) {
        Ok(repeated) => Ok((repeated, padded.size())),
        Err(e) => Err(e),
    }
}

/// Creates a layout for `n` instances of the value described by `layout`, with no padding between.
///
/// Note that, unlike [`repeat_layout`], `repeat_packed` doesn't guarantee that repeated
/// instances of the value described by `layout` will be properly aligned, even if `layout` is
/// properly aligned.
///
/// In other words, if the layout returned by`repeat_packed` is used to allocate an array, it isn't
/// guaranteed that all elements in the array will be properly aligned.
///
/// # Errors
///
/// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
/// - [`AllocError::ArithmeticOverflow`] if an arithmetic operation would overflow.
#[inline]
pub const fn repeat_layout_packed(
    layout: Layout,
    count: usize,
) -> Result<Layout, RepeatLayoutError> {
    #[allow(clippy::option_if_let_else)]
    let size = match checked_op(layout.size(), ArithOp::Mul, count) {
        Ok(s) => s,
        Err(e) => return Err(RepeatLayoutError::ArithmeticOverflow(e)),
    };
    let align = layout.align();
    match layout_from_size_align(size, align) {
        Ok(layout) => Ok(layout),
        Err(r) => Err(RepeatLayoutError::InvalidLayout(InvLayout(size, align, r))),
    }
}

/// Internal helper to check for a valid layout's size and alignment, returning a layout
/// using the provided size and alignment if they are valid, or the appropriate [`LayoutErr`].
#[inline]
#[cfg_attr(not(feature = "dev"), doc(hidden))]
pub const fn layout_from_size_align(size: usize, align: usize) -> Result<Layout, LayoutErr> {
    if align == 0 {
        return Err(LayoutErr::Align(AlignErr::ZeroAlign));
    } else if !align.is_power_of_two() {
        return Err(LayoutErr::Align(AlignErr::NonPowerOfTwoAlign(align)));
    } else if size > USIZE_HIGH_BIT - align {
        return Err(LayoutErr::Overflow);
    }

    // SAFETY: we just checked all of the invariants.
    Ok(unsafe { Layout::from_size_align_unchecked(size, align) })
}
