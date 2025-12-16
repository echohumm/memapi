use crate::{
    StdLayout,
    data::type_props::{PtrProps, SizedProps, USIZE_HIGH_BIT, USIZE_MAX_NO_HIGH_BIT},
    error::{AlignErr, ArithOp, InvLayout, LayoutErr, RepeatLayoutError},
    helpers::{
        align_up_unchecked,
        checked_op,
        dangling_nonnull_for,
        layout_extend,
        union_transmute
    }
};

const fn lay_from_size_align(size: usize, align: usize) -> Result<Layout, LayoutErr> {
    tri!(do check_lay(size, align));

    // SAFETY: we just validated the parameters
    Ok(unsafe { Layout::from_size_align_unchecked(size, align) })
}

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

const fn layout_or_sz_align<T>(n: usize) -> Result<Layout, (usize, usize, LayoutErr)> {
    let (sz, align) = (T::SZ, T::ALN);

    if sz != 0 && n > ((USIZE_MAX_NO_HIGH_BIT + 1) - align) / sz {
        return Err((sz, align, LayoutErr::ExceedsMax));
    }

    // SAFETY: we just validated that a layout with a size of `sz * n` and alignment of `align` will
    //  not overflow.
    unsafe { Ok(Layout::from_size_align_unchecked(sz * n, align)) }
}

#[allow(clippy::missing_errors_doc)]
const fn layout_or_err<T>(n: usize) -> Result<Layout, InvLayout> {
    match layout_or_sz_align::<T>(n) {
        Ok(l) => Ok(l),
        Err((sz, aln, r)) => Err(InvLayout(sz, aln, r))
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
        match layout_or_err::<T>(n) {
            Ok(l) => Ok(l),
            Err(e) => Err(RepeatLayoutError::InvalidLayout(e))
        }
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
        dangling_nonnull_for(*self)
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
    ///   [`USIZE_MAX_NO_HIGH_BIT`](USIZE_MAX_NO_HIGH_BIT).
    #[must_use]
    #[inline]
    pub const unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Layout {
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

    /// Converts this layout to a [`alloc::alloc::Layout`].
    #[must_use]
    #[inline]
    pub const fn to_stdlib(self) -> StdLayout {
        // SAFETY: we validate all layout's requirements ourselves
        // TODO: i'm torn between keeping or changing this to use a transmute like from_stdlib;
        //  higher safety or consistency
        unsafe { StdLayout::from_size_align_unchecked(self.size(), self.align()) }
    }

    /// Converts a [`alloc::alloc::Layout`] to a [`Layout`].
    ///
    /// Note that this is only `const` on Rust versions 1.56 and above.
    // this will never be const like this, but it will if i fully switch to this type from StdLayout
    #[rustversion::attr(since(1.56), const)]
    #[must_use]
    #[inline]
    pub fn from_stdlib(layout: StdLayout) -> Layout {
        // SAFETY: we share layout's requirements and, as checked by the build.rs, internal layout.
        unsafe { union_transmute::<StdLayout, Layout>(layout) }
    }
}
