use crate::{
    Layout,
    data::type_props::USIZE_HIGH_BIT,
    error::{AlignErr, LayoutErr}
};

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

/// Creates a [`Layout`] from the given size and alignment after checking their validity.
///
/// # Errors
///
/// See [`check_lay`].
#[cfg_attr(not(feature = "dev"), doc(hidden))]
pub const fn lay_from_size_align(size: usize, align: usize) -> Result<Layout, LayoutErr> {
    tri!(do check_lay(size, align));

    // SAFETY: we just validated the parameters
    Ok(unsafe { Layout::from_size_align_unchecked(size, align) })
}

/// Checks the validity of a size and alignment for being used in a [`Layout`]
///
/// # Errors
///
/// - <code>[LayoutErr::Align]([AlignErr::ZeroAlign])</code> if `align == 0`.
/// - <code>[LayoutErr::Align]([AlignErr::NonPowerOfTwoAlign])</code> if `!align.is_power_of_two`.
/// - [`LayoutErr::ExceedsMax`] if `size` rounded up to the nearest multiple of `align` would be
///   greater than [`USIZE_MAX_NO_HIGH_BIT`](crate::data::type_props::USIZE_MAX_NO_HIGH_BIT).
#[cfg_attr(not(feature = "dev"), doc(hidden))]
pub const fn check_lay(size: usize, align: usize) -> Result<(), LayoutErr> {
    if align == 0 {
        return Err(LayoutErr::Align(AlignErr::ZeroAlign));
    } else if !align.is_power_of_two() {
        return Err(LayoutErr::Align(AlignErr::NonPowerOfTwoAlign(align)));
    } else if size > USIZE_HIGH_BIT - align {
        return Err(LayoutErr::ExceedsMax);
    }
    Ok(())
}
