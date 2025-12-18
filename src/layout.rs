use crate::{
    StdLayout,
    data::type_props::{PtrProps, SizedProps, USIZE_HIGH_BIT, USIZE_MAX_NO_HIGH_BIT},
    error::{AlignErr, AllocError, ArithOp, Cause, InvLayout, LayoutErr, RepeatLayoutError},
    helpers::{
        align_up,
        align_up_unchecked,
        checked_op,
        dangling_nonnull,
        is_multiple_of,
        layout_extend
    }
};

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

/// The layout of a block of memory in the form of its size and alignment in bytes.
///
/// Note that this is `memapi`'s custom type, not stdlib's [`alloc::alloc::Layout`]. If a function
/// you want does not exist, request it in an issue.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Layout {
    size: usize,
    align: usize
}

impl PartialEq<StdLayout> for Layout {
    fn eq(&self, other: &StdLayout) -> bool {
        self.align == other.align() && self.size == other.size()
    }
}
impl PartialEq<Layout> for StdLayout {
    fn eq(&self, other: &Layout) -> bool {
        self.align() == other.align && self.size() == other.size
    }
}
impl From<StdLayout> for Layout {
    fn from(layout: StdLayout) -> Layout {
        Layout::from_stdlib(layout)
    }
}
impl From<Layout> for StdLayout {
    fn from(layout: Layout) -> StdLayout {
        layout.to_stdlib()
    }
}

impl Layout {
    /// Creates a layout for the given type.
    ///
    /// This just delegates to <code><T as [SizedProps>::LAYOUT]</code>.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    #[must_use]
    pub const fn new<T>() -> Layout {
        T::LAYOUT
    }

    /// Creates a layout representing an array of `n` `T`.
    ///
    /// # Errors
    ///
    /// See [`repeat_packed`](Layout::repeat_packed).
    pub const fn array<T>(n: usize) -> Result<Layout, RepeatLayoutError> {
        let (sz, align) = (T::SZ, T::ALN);

        if sz != 0 && n > ((USIZE_MAX_NO_HIGH_BIT + 1) - align) / sz {
            return Err(RepeatLayoutError::InvalidLayout(InvLayout(
                sz,
                align,
                LayoutErr::ExceedsMax
            )));
        }

        // SAFETY: we just validated that a layout with a size of `sz * n` and alignment of `align`
        // will not overflow.
        unsafe { Ok(Layout::from_size_align_unchecked(sz * n, align)) }
    }

    /// Combines two layouts sequentially, returning the combined layout and the
    /// offset where `other` begins.
    ///
    /// Given two layouts `self` and `other`, computes a layout describing a block of memory that
    /// can hold a value of layout `self` followed by a value of layout `other`, where `other`
    /// starts at an offset that satisfies its alignment. Returns the resulting combined layout and
    /// the offset at which `other` begins.
    ///
    /// This method delegates to [`helpers::layout_extend`](layout_extend).
    ///
    /// # Errors
    ///
    /// Returns [`InvLayout`] when the resulting size or alignment would exceed
    /// [`USIZE_MAX_NO_HIGH_BIT`] or when an intermediate arithmetic operation overflows.
    #[rustversion::attr(since(1.47), const)]
    pub fn extend(&self, other: Layout) -> Result<(Layout, usize), InvLayout> {
        layout_extend(*self, other)
    }

    /// Returns a valid, dangling pointer for this layout's alignment.
    ///
    /// The returned pointer is non-null and correctly aligned for types that use this layout's
    /// alignment but should not be dereferenced.
    #[must_use]
    #[inline]
    pub const fn dangling(&self) -> core::ptr::NonNull<u8> {
        // SAFETY: we validate dangling_nonnull's requirements at construction.
        unsafe { dangling_nonnull(self.align()) }
    }

    /// Creates a layout for the value behind the given reference
    ///
    /// This just delegates to <code><&T as [PtrProps>::layout()]</code>.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn for_value<T: ?Sized>(val: &T) -> Layout {
        // SAFETY: references are always valid
        unsafe { val.layout() }
    }

    /// Creates a layout for the value behind the given reference
    ///
    /// This just delegates to <code><*const T as [PtrProps>::layout()]</code>.
    ///
    /// # Safety
    ///
    /// Callers must ensure the pointer is:
    /// - non-null
    /// - non-dangling
    /// - aligned
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub unsafe fn for_value_raw<T: ?Sized>(val: *const T) -> Layout {
        val.layout()
    }

    //noinspection LongLine
    /// Creates a layout with the given size and alignment.
    ///
    /// # Errors
    ///
    /// - <code>LayoutErr::Align([AlignErr::ZeroAlign](AlignErr::ZeroAlign))</code> if `align == 0`.
    /// - <code>LayoutErr::Align([AlignErr::NonPowerOfTwoAlign](align))</code> if `align` is
    ///   non-zero, but not a power of two.
    /// - [`LayoutErr::ExceedsMax`] if `size` rounded up to the nearest multiple of `align` exceeds
    ///   [`USIZE_MAX_NO_HIGH_BIT`](USIZE_MAX_NO_HIGH_BIT).
    #[inline]
    pub const fn from_size_align(size: usize, align: usize) -> Result<Layout, LayoutErr> {
        tri!(do check_lay(size, align));

        // SAFETY: we just validated the parameters
        Ok(unsafe { Layout::from_size_align_unchecked(size, align) })
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
    ///   [`USIZE_MAX_NO_HIGH_BIT`](USIZE_MAX_NO_HIGH_BIT).
    #[must_use]
    #[inline]
    pub const unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Layout {
        assume!(
            check_lay(size, align).is_ok(),
            "values passed to `Layout::from_size_align_unchecked()` are invalid. size: {}, align: \
             {}",
            size,
            align
        );

        Layout { size, align }
    }

    /// Returns the size of this layout.
    #[must_use]
    #[inline]
    pub const fn size(&self) -> usize {
        self.size
    }

    /// Returns the alignment of this layout.
    #[must_use]
    #[inline]
    pub const fn align(&self) -> usize {
        self.align
    }

    /// Returns the amount of padding necessary after `self` to ensure that the following address
    /// will satisfy `align`.
    ///
    /// # Example
    ///
    /// ```
    /// # use memapi2::Layout;
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
        // SAFETY: constructors require that the size and alignment are valid for this operation.
        let aligned_sz = unsafe { align_up_unchecked(self.size(), self.align()) };
        // SAFETY: above.
        unsafe { Layout::from_size_align_unchecked(aligned_sz, self.align()) }
    }

    /// Creates a layout for `n` instances of the value described by `layout`, with padding between
    /// each to ensure that each instance is given its requested size and alignment.
    ///
    /// On success, returns `(l, offs)` where `l` is the layout of the array and `offs` is the
    /// distance between the start of each element in the array (stride).
    ///
    /// Note that this is only `const` on Rust versions 1.47 and above.
    ///
    /// # Errors
    ///
    /// - [`RepeatLayoutError::InvalidLayout`] if the computed layout is invalid.
    /// - [`RepeatLayoutError::ArithmeticOverflow`] if an arithmetic operation would overflow.
    #[rustversion::attr(since(1.47), const)]
    #[inline]
    pub fn repeat(&self, count: usize) -> Result<(Layout, usize), RepeatLayoutError> {
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
    /// Note that this is only `const` on Rust versions 1.47 and above.
    ///
    /// # Errors
    ///
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ArithmeticOverflow`] if an arithmetic operation would overflow.
    #[rustversion::attr(since(1.47), const)]
    #[inline]
    pub fn repeat_packed(&self, count: usize) -> Result<Layout, RepeatLayoutError> {
        #[allow(clippy::option_if_let_else)]
        let size = match checked_op(self.size(), ArithOp::Mul, count) {
            Ok(s) => s,
            Err(e) => return Err(RepeatLayoutError::ArithmeticError(e))
        };
        let align = self.align();
        match Layout::from_size_align(size, align) {
            Ok(layout) => Ok(layout),
            Err(e) => Err(RepeatLayoutError::InvalidLayout(InvLayout(size, align, e)))
        }
    }

    //noinspection LongLine
    /// Creates a layout with the same size as `self` but an alignment meeting `align`. If
    /// `self.align >= align`, returns `self`.
    ///
    /// This method doesn't modify the size of the new layout.
    ///
    /// # Errors
    ///
    /// - <code>LayoutErr::Align([AlignErr::NonPowerOfTwoAlign(align)](AlignErr::NonPowerOfTwoAlign))</code> if `align` is larger than `self.align`, but not a power of two.
    /// - [`LayoutErr::ExceedsMax`] if `size` rounded up to the nearest multiple of `align` exceeds
    ///   [`USIZE_MAX_NO_HIGH_BIT`].
    #[must_use = "this function returns a new layout, it doesn't modify the original one"]
    #[allow(clippy::double_must_use)]
    #[inline]
    pub const fn align_to(&self, align: usize) -> Result<Layout, LayoutErr> {
        if align > self.align() { Layout::from_size_align(self.size(), align) } else { Ok(*self) }
    }

    /// Returns a layout with the same `size` as `self` but whose alignment has been rounded up to
    /// the nearest multiple of `align`.
    ///
    /// This differs from [`Layout::align_to`]: `align_to` sets the layout's alignment to the
    /// provided alignment if that alignment is larger than the current one. This method instead
    /// rounds the current alignment up to a multiple of the provided `align`.
    ///
    /// # Errors
    ///
    /// Propagates the error returned by [`Layout::from_size_align`] if construction of the new
    /// layout fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use memapi2::Layout;
    /// // current alignment 8, round up to a multiple of 6 => next multiple is 12
    /// let l = unsafe { Layout::from_size_align_unchecked(30, 8) };
    /// let rounded = l.align_to_multiple_of(16).unwrap();
    /// assert_eq!(rounded.align(), 16);
    /// assert_eq!(rounded.size(), 30);
    /// ```
    #[inline]
    pub const fn align_to_multiple_of(&self, align: usize) -> Result<Layout, InvLayout> {
        let cur_align = self.align();
        if is_multiple_of(cur_align, align) {
            Ok(*self)
        } else {
            let new_align = tri!(do align_up(cur_align, align));
            match Layout::from_size_align(self.size(), new_align) {
                Ok(l) => Ok(l),
                Err(e) => Err(InvLayout(self.size(), new_align, e))
            }
        }
    }

    /// Produce a layout that is compatible with C's `aligned_alloc` requirements.
    ///
    /// C's `aligned_alloc(alignment, size)` requires:
    /// - `alignment` is a power of two, non-zero, and a multiple of `size_of::<*mut c_void>()`.
    /// - `size` is a multiple of `alignment`.
    ///
    /// # Errors
    ///
    /// Returns `Err(AllocError::AllocFailed(layout, Cause::CRoundUp))` if the alignment-rounding
    /// step fails. See [`Layout::align_to_multiple_of`] (the function used for rounding).
    #[inline]
    pub const fn to_aligned_alloc_compatible(&self) -> Result<Layout, AllocError> {
        // first, make the alignment a multiple of `size_of::<*mut c_void>()`.
        let aligned = match self.align_to_multiple_of(usize::SZ) {
            Ok(l) => l,
            Err(_) => return Err(AllocError::AllocFailed(*self, Cause::CRoundUp))
        };
        // then pad the size up to a multiple of the new alignment
        Ok(aligned.pad_to_align())
    }

    /// Converts this layout to an [`alloc::alloc::Layout`].
    #[must_use]
    #[inline]
    pub const fn to_stdlib(self) -> StdLayout {
        // SAFETY: we validate all layout's requirements ourselves
        unsafe { StdLayout::from_size_align_unchecked(self.size(), self.align()) }
    }

    /// Converts an [`alloc::alloc::Layout`] to a [`Layout`].
    ///
    /// Note that this is only `const` on Rust versions 1.50 and above.
    #[rustversion::attr(since(1.50), const)]
    #[must_use]
    #[inline]
    pub fn from_stdlib(layout: StdLayout) -> Layout {
        // SAFETY: we share layout's requirements and, as checked by the build.rs, internal layout.
        unsafe { Layout::from_size_align_unchecked(layout.size(), layout.align()) }
    }
}
