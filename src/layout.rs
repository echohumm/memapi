use crate::{
    StdLayout,
    data::type_props::{PtrProps, SizedProps},
    error::{ArithOp, Error, LayoutErr},
    helpers::{
        USIZE_HIGH_BIT,
        USIZE_MAX_NO_HIGH_BIT,
        align_up,
        checked_op,
        dangling_nonnull,
        is_multiple_of
    }
};

const fn align_up_checked(val: usize, align: usize) -> Result<usize, Error> {
    tri!(do check_lay(val, align));

    Ok(align_up(val, align))
}

const fn check_lay(size: usize, align: usize) -> Result<(), Error> {
    if align == 0 {
        return Err(Error::InvalidLayout(size, align, LayoutErr::ZeroAlign));
    } else if !align.is_power_of_two() {
        return Err(Error::InvalidLayout(size, align, LayoutErr::NonPowerOfTwoAlign));
    } else if size > USIZE_HIGH_BIT - align {
        return Err(Error::InvalidLayout(size, align, LayoutErr::ExceedsMax));
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

    // TODO: can be deduped with repeat_packed, decide whether or not to
    /// Creates a layout representing an array of `n` `T`.
    ///
    /// # Errors
    ///
    /// Returns <code>Err([Error::InvalidLayout]\([T::SZ], [T::ALN],
    /// [LayoutErr:ExceedsMax]\))</code> if the length of the computed array, in bytes, would
    /// exceed [`USIZE_MAX_NO_HIGH_BIT`].
    pub const fn array<T>(n: usize) -> Result<Layout, Error> {
        let (sz, align) = (T::SZ, T::ALN);

        if sz != 0 && n > (USIZE_HIGH_BIT - align) / sz {
            return Err(Error::InvalidLayout(sz, align, LayoutErr::ExceedsMax));
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
    /// Note that this is only `const` on Rust versions 1.47 and above.
    ///
    /// # Errors
    ///
    /// Returns <code>Err([Error::InvalidLayout]\([self.size()](Layout::size),
    /// [other.align()](Layout::align), [LayoutErr::ExceedsMax]\))</code> if
    /// [`self.size()`](Layout::size) rounded up to the nearest multiple of
    /// [`other.align()`](Layout::align) would exceed [`USIZE_MAX_NO_HIGH_BIT`].
    #[rustversion::attr(since(1.47), const)]
    pub fn extend(&self, other: Layout) -> Result<(Layout, usize), Error> {
        let a_sz = self.size();
        let a_aln = self.align();
        let b_aln = other.align();

        // compute the offset where `b` would start when placed after `a`, aligned for `b`.
        // SAFETY: `Layout::align()` is always non-zero and a power of two.
        let offset = tri!(do align_up_checked(a_sz, b_aln));

        // i love how max, possibly the simplest function in existence (aside from accessors), is
        // not const.
        let new_align = if a_aln > b_aln { a_aln } else { b_aln };

        // check the total size fits within limits and doesn't overflow.
        match checked_op(a_sz, ArithOp::Add, offset) {
            Ok(total) if total <= USIZE_MAX_NO_HIGH_BIT => {
                // SAFETY: we validated alignment and size constraints above.
                Ok((unsafe { Layout::from_size_align_unchecked(total, new_align) }, offset))
            }
            Err(e) => Err(Error::InvalidLayout(offset, new_align, LayoutErr::ArithErr(e))),
            _ => Err(Error::InvalidLayout(offset, new_align, LayoutErr::ExceedsMax))
        }
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
    /// - <code>Err([Error::InvalidLayout]\(size, align, [LayoutErr::ExceedsMax]\))</code> if `size`
    ///   rounded up to the nearest multiple of `align` would exceed [`USIZE_MAX_NO_HIGH_BIT`].
    /// - <code>Err([Error::InvalidLayout]\(size, align, [LayoutErr::ZeroAlign]\))</code> if `align
    ///   == 0`.
    /// - <code>Err([Error::InvalidLayout]\(size, align, [LayoutErr::NonPowerOfTwoAlign]\))</code>
    ///   if `align` is not a power of two.
    #[inline]
    pub const fn from_size_align(size: usize, align: usize) -> Result<Layout, Error> {
        tri!(do check_lay(size, align));

        // SAFETY: we just validated the parameters
        Ok(unsafe { Layout::from_size_align_unchecked(size, align) })
    }

    // TODO: docs for this function.

    /// <placeholder docs>
    pub const fn aligned_alloc_compatible_from_size_align(
        size: usize,
        align: usize
    ) -> Result<Layout, Error> {
        let align_rounded = tri!(do align_up_checked(align, usize::SZ));
        if size > USIZE_HIGH_BIT - align_rounded {
            return Err(Error::InvalidLayout(size, align_rounded, LayoutErr::ExceedsMax));
        }
        // SAFETY: we just checked that it would be valid
        let aligned_sz = unsafe { align_up(size, align_rounded) };
        match Layout::from_size_align(aligned_sz, align_rounded) {
            Ok(l) => Ok(l),
            Err(e) => Err(e)
        }
    }

    /// Creates a layout with the given size and alignment.
    ///
    /// In debug mode, this will panic if passed an invalid size or alignment.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `align` is a non-zero power of two.
    /// - `size` rounded up to `align` does not exceed [`USIZE_MAX_NO_HIGH_BIT`].
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
    /// # Errors
    ///
    /// Returns <code>Err([LayoutErr::NonPowerOfTwoAlign])</code> if `align` is not a power of two.
    ///
    /// # Example
    ///
    /// ```
    /// # use memapi2::Layout;
    ///
    /// assert_eq!(unsafe { Layout::from_size_align_unchecked(6, 8) }.padding_needed_for(8), 2);
    /// ```
    #[inline]
    pub const fn padding_needed_for(&self, align: usize) -> Result<usize, LayoutErr> {
        if !align.is_power_of_two() {
            return Err(LayoutErr::NonPowerOfTwoAlign);
        }

        let sz = self.size();
        // SAFETY: we just checked that the alignment was valid
        Ok(unsafe { align_up(sz, align) - sz })
    }

    /// Creates a layout by rounding the size of this layout up to a multiple of the layout's
    /// alignment.
    ///
    /// This is equivalent to adding the result of [`Layout::padding_needed_for`] to the layout's
    /// current size.
    #[must_use]
    #[inline]
    pub const fn pad_to_align(&self) -> Layout {
        // SAFETY: constructors require that the size and alignment are valid for this operation.
        let aligned_sz = unsafe { align_up(self.size(), self.align()) };
        // SAFETY: above.
        unsafe { Layout::from_size_align_unchecked(aligned_sz, self.align()) }
    }

    /// Creates a layout for `count` instances of the value described by `layout`, with padding
    /// between each to ensure that each instance is given its requested size and alignment.
    ///
    /// On success, returns `(l, offs)` where `l` is the layout of the array and `offs` is the
    /// distance between the start of each element in the array (stride).
    ///
    /// Note that this is only `const` on Rust versions 1.47 and above.
    ///
    /// # Errors
    ///
    /// Propagates the error from
    /// <code>[Layout::repeat_packed]\([self.pad_to_align()](Layout::pad_to_align), count\)</code>
    /// if it fails
    #[rustversion::attr(since(1.47), const)]
    #[inline]
    pub fn repeat(&self, count: usize) -> Result<(Layout, usize), Error> {
        let padded = self.pad_to_align();
        match padded.repeat_packed(count) {
            Ok(repeated) => Ok((repeated, padded.size())),
            Err(e) => Err(e)
        }
    }

    /// Creates a layout for `count` instances of the value described by `layout`, with no padding
    /// between.
    ///
    /// Note that, unlike [`Layout::repeat`], `repeat_packed` doesn't guarantee that repeated
    /// instances of the value described by `layout` will be properly aligned, even if `layout` is
    /// properly aligned.
    ///
    /// In other words, if the layout returned by`repeat_packed` is used to allocate an array, it
    /// isn't guaranteed that all elements in the array will be properly aligned.
    ///
    /// Note that this is only `const` on Rust versions 1.47 and above.
    #[rustversion::attr(since(1.47), const)]
    #[inline]
    pub fn repeat_packed(&self, count: usize) -> Result<Layout, Error> {
        #[allow(clippy::option_if_let_else)]
        let size = match checked_op(self.size(), ArithOp::Mul, count) {
            Ok(s) => s,
            Err(e) => return Err(Error::ArithmeticError(e))
        };
        let align = self.align();
        match Layout::from_size_align(size, align) {
            Ok(layout) => Ok(layout),
            Err(e) => Err(e)
        }
    }

    //noinspection LongLine
    /// Creates a layout with the same size as `self` but an alignment meeting `align`. If
    /// <code>[self.align()](Layout::align) >= align</code>, returns `self`.
    ///
    /// This method doesn't modify the size of the new layout.
    ///
    /// # Errors
    ///
    /// Propagates the error from <code>[Layout::from_size_align]\([self.size](Layout::size),
    /// align\)</code> if it fails.
    #[must_use = "this function returns a new layout, it doesn't modify the original one"]
    #[allow(clippy::double_must_use)]
    #[inline]
    pub const fn align_to(&self, align: usize) -> Result<Layout, Error> {
        if align > self.align() { Layout::from_size_align(self.size(), align) } else { Ok(*self) }
    }

    /// Returns a layout with the same `size` as `self` but whose alignment has been rounded up to
    /// the nearest multiple of `align`.
    ///
    /// This differs from [`Layout::align_to`]: [`align_to`](Layout::align_to) sets the layout's
    /// alignment to the provided alignment if that alignment is larger than the current one.
    /// This method instead rounds the current alignment up to a multiple of the provided
    /// `align`.
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
    pub const fn align_to_multiple_of(&self, align: usize) -> Result<Layout, Error> {
        let cur_align = self.align();
        if is_multiple_of(cur_align, align) {
            Ok(*self)
        } else {
            Layout::from_size_align(self.size(), tri!(do align_up_checked(cur_align, align)))
        }
    }

    /// Produce a layout that is compatible with C's `aligned_alloc` requirements.
    ///
    /// C's `aligned_alloc(alignment, size)` requires:
    /// - `alignment` is a power of two, non-zero, and a multiple of <code>[size_of]::<*mut
    ///   [c_void]>()</code>.
    /// - `size` is a multiple of `alignment`.
    ///
    /// # Errors
    ///
    /// Returns <code>Err([Error::InvalidLayout]\([self.size()](Layout::size),
    /// [self.align()](Layout::align), [LayoutErr::CRoundUp]\))</code> if the call to
    /// <code>[self.align_to_multiple_of](Layout::align_to_multiple_of)\([usize::SZ]\)</code> fails.
    #[inline]
    pub const fn to_aligned_alloc_compatible(&self) -> Result<Layout, Error> {
        // first, make the alignment a multiple of `size_of::<*mut c_void>()`.
        let aligned = match self.align_to_multiple_of(usize::SZ) {
            Ok(l) => l,
            Err(_) => {
                return Err(Error::InvalidLayout(self.size(), self.align(), LayoutErr::CRoundUp));
            }
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
