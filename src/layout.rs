use crate::{
    error::{ArithOp, InvLayout, LayoutErr, RepeatLayoutError},
    helpers::{align_up_unchecked, checked_op, layout_or_err},
    data::type_props::{PtrProps, SizedProps},
    unstable_util::lay_from_size_align
};

/// The layout of a block of memory in the form of its size and alignment in bytes.
///
/// Note that this is `memapi`'s custom type to avoid importing the `alloc` crate. Its performance
/// cannot be guaranteed relative to stdlib's version. Use should be avoided.
///
/// This type is being used because the `no_alloc` feature is on.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Layout {
    size: usize,
    align: usize
}

impl Layout {
    /// Creates a layout for the given type.
    ///
    /// This just delegates to `<T as `[`SizedProps>::LAYOUT`].
    #[allow(clippy::inline_always)]
    #[inline(always)]
    #[must_use]
    pub const fn new<T>() -> Layout { T::LAYOUT }

    /// Creates a layout representing an array of `n` `T`.
    ///
    /// # Errors
    ///
    /// See [`repeat_packed`](Layout::repeat_packed).
    pub const fn array<T>(n: usize) -> Result<Layout, RepeatLayoutError> {
        match layout_or_err::<T>(n) {
            Ok(l) => Ok(l),
            Err(e) => Err(RepeatLayoutError::InvalidLayout(e))
        }
    }

    /// Creates a layout for the value behind the given reference
    ///
    /// This just delegates to `<&T as `[`PtrProps>::layout()`].
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn for_value<T: ?Sized>(val: &T) -> Layout {
        // SAFETY: references are always valid
        unsafe { val.layout() }
    }

    /// Creates a layout for the value behind the given reference
    ///
    /// This just delegates to `<*const T as `[`PtrProps>::layout()`].
    ///
    /// # Safety
    ///
    /// Callers must ensure the pointer is:
    /// - non-null
    /// - non-dangling
    /// - aligned
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub unsafe fn for_value_raw<T: ?Sized>(val: *const T) -> Layout { val.layout() }

    /// Creates a layout with the given size and alignment.
    ///
    /// # Errors
    ///
    /// - `LayoutErr::Align(`[`AlignErr::ZeroAlign`](crate::error::AlignErr::ZeroAlign)`)` if `align
    ///   == 0`.
    /// - `LayoutErr::Align(`
    ///   [`AlignErr::NonPowerOfTwoAlign(align)`](crate::error::AlignErr::NonPowerOfTwoAlign)`)` if
    ///   `align` is non-zero, but not a power of two.
    /// - [`LayoutErr::ExceedsMax`] if `size` rounded up to the nearest multiple of `align` exceeds
    ///   [`USIZE_MAX_NO_HIGH_BIT`](crate::data::type_props::USIZE_MAX_NO_HIGH_BIT).
    #[inline]
    pub const fn from_size_align(size: usize, align: usize) -> Result<Layout, LayoutErr> {
        lay_from_size_align(size, align)
    }

    /// Creates a layout with the given size and alignment.
    ///
    /// In debug mode, this will panic if passed an invalid size or alignment.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `align` is a non-zero power of two.
    /// - `size` rounded up to `align` does not exceed
    ///   [`USIZE_MAX_NO_HIGH_BIT`](crate::data::type_props::USIZE_MAX_NO_HIGH_BIT).
    #[must_use]
    #[inline]
    pub const unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Layout {
        assume!(crate::unstable_util::check_lay(size, align).is_ok());

        Layout { size, align }
    }

    /// Returns the size of this layout.
    #[must_use]
    #[inline]
    pub const fn size(&self) -> usize { self.size }

    /// Returns the alignment of this layout.
    #[must_use]
    #[inline]
    pub const fn align(&self) -> usize { self.align }

    /// Returns the amount of padding necessary after `self` to ensure that the following address
    /// will satisfy `align`.
    ///
    /// # Example
    ///
    /// ```
    /// # use memapi::Layout;
    ///
    /// assert_eq!(unsafe { Layout::from_size_align_unchecked(6, 8) }.padding_needed_for(8), 2);
    /// ```
    #[must_use]
    #[inline]
    pub const fn padding_needed_for(&self, align: usize) -> usize {
        if !align.is_power_of_two() {
            return usize::MAX;
        }

        let sz = self.size();
        // SAFETY: we just checked that the alignment was valid
        unsafe { align_up_unchecked(sz, align) - sz }
    }

    /// Creates a layout by rounding the size of this layout up to a multiple of the layout's
    /// alignment.
    ///
    /// This is equivalent to adding the result of [`layout_padding_for`] to the layout's current
    /// size.
    #[must_use]
    #[inline]
    pub const fn pad_to_align(&self) -> Layout {
        // SAFETY: layout's requirements guarantee that the rounded up size is valid.
        unsafe {
            Layout::from_size_align_unchecked(
                align_up_unchecked(self.size(), self.align()),
                self.align()
            )
        }
    }

    /// Creates a layout for `n` instances of the value described by `layout`, with padding between
    /// each to ensure that each instance is given its requested size and alignment.
    ///
    /// On success, returns `(l, offs)` where `l` is the layout of the array and `offs` is the
    /// distance between the start of each element in the array (stride).
    ///
    /// # Errors
    ///
    /// - [`RepeatLayoutError::InvalidLayout`] if the computed layout is invalid.
    /// - [`RepeatLayoutError::ArithmeticOverflow`] if an arithmetic operation would overflow.
    #[inline]
    pub const fn repeat(&self, count: usize) -> Result<(Layout, usize), RepeatLayoutError> {
        let padded = self.pad_to_align();
        match padded.repeat_packed(count) {
            Ok(repeated) => Ok((repeated, padded.size())),
            Err(e) => Err(e)
        }
    }

    /// Creates a layout for `n` instances of the value described by `layout`, with no padding
    /// between.
    ///
    /// Note that, unlike [`repeat_layout`], `repeat_packed` doesn't guarantee that repeated
    /// instances of the value described by `layout` will be properly aligned, even if `layout` is
    /// properly aligned.
    ///
    /// In other words, if the layout returned by`repeat_packed` is used to allocate an array, it
    /// isn't guaranteed that all elements in the array will be properly aligned.
    ///
    /// # Errors
    ///
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ArithmeticOverflow`] if an arithmetic operation would overflow.
    #[inline]
    pub const fn repeat_packed(&self, count: usize) -> Result<Layout, RepeatLayoutError> {
        #[allow(clippy::option_if_let_else)]
        let size = match checked_op(self.size(), ArithOp::Mul, count) {
            Ok(s) => s,
            Err(e) => return Err(RepeatLayoutError::ArithmeticOverflow(e))
        };
        let align = self.align();
        match Layout::from_size_align(size, align) {
            Ok(layout) => Ok(layout),
            Err(e) => Err(RepeatLayoutError::InvalidLayout(InvLayout(size, align, e)))
        }
    }

    /// Creates a layout with the same size as `self` but an alignment meeting `align`. If
    /// `self.align >= align`, returns `self`.
    ///
    /// This method doesn't modify the size of the new layout.
    ///
    /// # Errors
    ///
    /// - `LayoutErr::Align(`
    ///   [`AlignErr::NonPowerOfTwoAlign(align)`](crate::error::AlignErr::NonPowerOfTwoAlign)`)` if
    ///   `align` is larger than `self.align`, but not a power of two.
    /// - [`LayoutErr::ExceedsMax`] if `size` rounded up to the nearest multiple of `align` exceeds
    ///   [`USIZE_MAX_NO_HIGH_BIT`](crate::data::type_props::USIZE_MAX_NO_HIGH_BIT).
    #[must_use = "this function returns a new layout, it doesn't modify the original one"]
    #[allow(clippy::double_must_use)]
    #[inline]
    pub const fn align_to(&self, align: usize) -> Result<Layout, LayoutErr> {
        if align > self.align() { Layout::from_size_align(self.size(), align) } else { Ok(*self) }
    }

    #[cfg(not(feature = "no_alloc"))]
    /// Converts this layout to a [`stdlib layout`](alloc::alloc::Layout).
    #[inline]
    pub const fn to_stdlib(self) -> alloc::alloc::Layout {
        // SAFETY: we validate all layout's requirements ourselves
        unsafe { core::mem::transmute::<Layout, alloc::alloc::Layout>(self) }
    }

    #[cfg(not(feature = "no_alloc"))]
    /// Converts a [`stdlib layout`](alloc::alloc::Layout) to a [`Layout`].
    #[inline]
    pub const fn from_stdlib(layout: alloc::alloc::Layout) -> Layout {
        // SAFETY: we share layout's requirements
        unsafe { core::mem::transmute::<alloc::alloc::Layout, Layout>(layout) }
    }
}
