use crate::{
    error::{AlignErr, LayoutErr},
    type_props::USIZE_HIGH_BIT,
    Layout,
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

#[cfg_attr(not(feature = "dev"), doc(hidden))]
pub const fn lay_from_size_align(size: usize, align: usize) -> Result<Layout, LayoutErr> {
    tri!(do check_lay(size, align));

    // SAFETY: we just validated the parameters
    Ok(unsafe { Layout::from_size_align_unchecked(size, align) })
}

#[cfg_attr(not(feature = "dev"), doc(hidden))]
pub const fn check_lay(size: usize, align: usize) -> Result<(), LayoutErr> {
    if align == 0 {
        return Err(LayoutErr::Align(AlignErr::ZeroAlign));
    } else if !align.is_power_of_two() {
        return Err(LayoutErr::Align(AlignErr::NonPowerOfTwoAlign(align)));
    } else if size > USIZE_HIGH_BIT - align {
        return Err(LayoutErr::Overflow);
    }
    Ok(())
}
