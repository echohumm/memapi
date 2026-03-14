use crate::traits::data::type_props::KnownAlign;
use {
    crate::{
        error::{ArithErr, ArithOp, LayoutErr},
        helpers::{USIZE_HIGH_BIT, USIZE_MAX_NO_HIGH_BIT, align_up, is_multiple_of, void_ptr},
        traits::data::type_props::{PtrProps, SizedProps}
    },
    ::core::{
        cmp::PartialEq,
        convert::From,
        marker::Sized,
        ptr::NonNull,
        result::Result::{self, Err, Ok}
    }
};

// sorry if docs are a little off, ngl i had gpt update the errors because it would be annoying so
// yeah

#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
/// A type alias for [`alloc::alloc::Layout`](::stdalloc::alloc::Layout).
pub type StdLayout = ::stdalloc::alloc::Layout;

#[inline]
const fn align_up_checks(sz: usize, aln: usize) -> Result<(), LayoutErr> {
    if aln == 0 {
        return Err(LayoutErr::ZeroAlign);
    } else if !aln.is_power_of_two() {
        return Err(LayoutErr::NonPowerOfTwoAlign(aln));
    } else if sz > USIZE_MAX_NO_HIGH_BIT - (aln - 1) {
        return Err(LayoutErr::ExceedsMax(sz, aln, 1));
    }

    Ok(())
}

#[cfg_attr(any(miri, debug_assertions), track_caller)]
const fn align_up_checked(size: usize, align: usize) -> Result<usize, LayoutErr> {
    tri!(do align_up_checks(size, align));

    // SAFETY: check_lay validates that `align != 0` so no underflow can occur, and `size + align`
    // won't exceed either `USIZE_HIGH_BIT` or `usize::MAX` so no overflow can occur, as well as
    // that `align` is a power of 2 so the alignment trick used by `align_up` works.
    Ok(unsafe { align_up(size, align) })
}

/// The layout of a block of memory in the form of its size and alignment in bytes.
///
/// Note that this is `memapi`'s custom type, not stdlib's
/// [`alloc::alloc::Layout`](::stdalloc::alloc::Layout). If a function you want does not exist,
/// request it in an issue.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Layout {
    size: usize,
    align: usize
}

#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
impl PartialEq<StdLayout> for Layout {
    fn eq(&self, other: &StdLayout) -> bool {
        self.align == other.align() && self.size == other.size()
    }
}
#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
impl PartialEq<Layout> for StdLayout {
    fn eq(&self, other: &Layout) -> bool {
        self.align() == other.align && self.size() == other.size
    }
}
#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
impl From<StdLayout> for Layout {
    #[cfg_attr(any(miri, debug_assertions), track_caller)]
    fn from(layout: StdLayout) -> Layout {
        Layout::from_stdlib(layout)
    }
}
#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
impl From<Layout> for StdLayout {
    #[cfg_attr(any(miri, debug_assertions), track_caller)]
    fn from(layout: Layout) -> StdLayout {
        layout.to_stdlib()
    }
}

impl Layout {
    /// Creates a layout for the given type.
    #[inline(always)]
    #[must_use]
    pub const fn new<T>() -> Layout {
        // SAFETY: the size and alignment of a sized type cannot be invalid for a layout
        unsafe { Layout::from_size_align_unchecked(T::SZ, T::ALN) }
    }

    // could be deduped with repeat*, but stdlib doesn't, and it's logically meaningfully faster, so
    // i won't
    /// Attempts to create a layout representing an array of `n` count `T`.
    ///
    /// # Errors
    ///
    /// <code>Err([LayoutErr::ExceedsMax]\([T::SZ](SizedProps::SZ), [T::ALN](KnownAlign::ALN),
    /// n\))</code> if the length of the computed array, in bytes, would
    /// exceed [`USIZE_MAX_NO_HIGH_BIT`].
    pub const fn array<T>(n: usize) -> Result<Layout, LayoutErr> {
        if T::SZ != 0 && n > (USIZE_HIGH_BIT - T::ALN) / T::SZ {
            return Err(LayoutErr::ExceedsMax(T::SZ, T::ALN, n));
        }

        // SAFETY: we just validated that a layout with a size of `T::SZ * n` and alignment of
        // `align` will not overflow.
        unsafe { Ok(Layout::array_unchecked::<T>(n)) }
    }

    /// Creates a layout representing an array of `n` count `T`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that <code>[T::SZ](SizedProps::SZ) * n</code> rounded up to
    /// [`T::ALN`](KnownAlign::ALN) will not exceed [`USIZE_MAX_NO_HIGH_BIT`].
    ///
    /// Additionally, the return value may be unexpected if <code>[T::SZ](SizedProps::SZ) * n</code>
    /// overflows.
    #[cfg_attr(any(miri, debug_assertions), track_caller)]
    #[must_use]
    #[inline]
    pub const unsafe fn array_unchecked<T>(n: usize) -> Layout {
        // god im bad at basic logic, i spent like 20 minutes trying to get this right because i
        // didn't want to write a test and just do trial and error. luckily now i think i have the
        // mental circuits for de morgan's laws down
        assert_unsafe_precondition!(
            "`Layout::array_unchecked` requires that `T::SZ * n` rounded up to `T::ALN` will not \
             exceed `USIZE_MAX_NO_HIGH_BIT`.",
            <T>(n: usize = n) => [T::SZ == 0 || n <= (USIZE_HIGH_BIT - T::ALN) / T::SZ]
        );
        Layout::from_size_align_unchecked(T::SZ * n, T::ALN)
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
    /// <code>Err([LayoutErr::ExceedsMax]\(#note, #note, 1\))</code> if
    /// [`self.size()`](Layout::size) rounded up to the nearest multiple of
    /// [`other.align()`](Layout::align) would exceed [`USIZE_MAX_NO_HIGH_BIT`].
    ///
    /// # note
    ///
    /// regarding the notes in the error section above.. please just look at the code to understand
    /// what those values are if you're using this before i figure out a way to express what those
    /// will be without just rewriting the function in the docs.
    pub const fn extend(&self, other: Layout) -> Result<(Layout, usize), LayoutErr> {
        let a_sz = self.size();
        let a_aln = self.align();
        let b_aln = other.align();

        // compute the offset where `b` would start when placed after `a`, aligned for `b`.
        // SAFETY: align is always non-zero and a power of two, size is at most
        // `isize::MAX`, so adding `align - 1` (which is at most `isize::MAX`) can never overflow.
        let offset = unsafe { align_up(a_sz, b_aln) };

        // new data must be aligned to the larger alignment to align both values.
        let new_align = if a_aln > b_aln { a_aln } else { b_aln };

        // compute the new total size. as each is at most `isize::MAX`, this can't overflow
        let total = a_sz + offset;
        // check the total size fits within limits and doesn't overflow.
        if total > USIZE_MAX_NO_HIGH_BIT - new_align {
            return Err(LayoutErr::ExceedsMax(total, new_align, 1));
        }
        // SAFETY: we validated alignment and size constraints above.
        Ok((unsafe { Layout::from_size_align_unchecked(total, new_align) }, offset))
    }

    /// Returns a valid, [dangling](::core::ptr::dangling) pointer for this layout's alignment.
    ///
    /// The returned pointer is non-null and correctly aligned for types that use this layout's
    /// alignment but should not be dereferenced.
    #[must_use]
    #[inline]
    pub const fn dangling(&self) -> NonNull<u8> {
        // SAFETY: we validate dangling_nonnull's requirements at construction.
        unsafe { NonNull::new_unchecked(self.align() as *mut u8) }
    }

    /// Creates a layout for the value behind the given reference
    #[inline(always)]
    pub fn for_value<T: ?Sized>(refer: &T) -> Layout {
        // SAFETY: references are always valid for `sz()`/`aln()`
        unsafe { refer.layout() }
    }

    /// Creates a layout for the value behind the given reference
    ///
    /// # Safety
    ///
    /// The caller must ensure the pointer is:
    /// - non-null
    /// - non-dangling
    /// - aligned
    #[cfg_attr(any(miri, debug_assertions), track_caller)]
    #[inline(always)]
    pub unsafe fn for_value_raw<T: ?Sized>(ptr: *const T) -> Layout {
        // no good way to check if a pointer is dangling/aligned without intrinsics/language
        // features we cant use, but we can at least check its non-null
        assert_unsafe_precondition!(
            noconst,
            "`Layout::for_value_raw` requires that `ptr` is non-null.",
            <T: [?Sized]>(ptr: *const T = ptr) => [!ptr.is_null()]
        );
        // SAFETY: caller guarantees that `ptr` meets the safety constraints of `layout()`.
        unsafe { ptr.layout() }
    }

    /// Creates a layout with the given size and alignment.
    ///
    /// # Errors
    ///
    /// - <code>Err([LayoutErr::ZeroAlign])</code> if `align == 0`.
    /// - <code>Err([LayoutErr::NonPowerOfTwoAlign]\(align\))</code> if `align` is not a power of
    ///   two.
    /// - <code>Err([LayoutErr::ExceedsMax]\(size, align, 1\))</code> if `size` rounded up to the
    ///   nearest multiple of `align` would exceed [`USIZE_MAX_NO_HIGH_BIT`].
    #[inline]
    pub const fn from_size_align(size: usize, align: usize) -> Result<Layout, LayoutErr> {
        tri!(do align_up_checks(size, align));

        // SAFETY: we just validated the parameters
        Ok(unsafe { Layout::from_size_align_unchecked(size, align) })
    }

    /// Creates a layout compatible with C's `posix_memalign` requirements from the given `size` and
    /// `align`.
    ///
    /// C's `posix_memalign(out, alignment, size)` requires `alignment` is a power of two, non-zero,
    /// and a multiple of <code>[void_ptr]::[SZ](SizedProps::SZ)</code>.
    ///
    /// Therefore, the alignment will be rounded up to the nearest multiple of
    /// <code>[void_ptr]::[SZ](SizedProps::SZ)</code> if it isn't already.
    ///
    /// [size_of]: ::core::mem::size_of
    ///
    /// # Errors
    ///
    /// - <code>Err([LayoutErr::ZeroAlign])</code> if `align == 0`.
    /// - <code>Err([LayoutErr::NonPowerOfTwoAlign]\(align\))</code> if `align` is not a power of
    ///   two.
    /// - <code>Err([LayoutErr::CRoundUp]\(align\))</code> if `align`, when rounded up to the
    ///   nearest multiple of <code>[void_ptr]::[SZ](SizedProps::SZ)</code>, would overflow
    ///   [`usize::MAX`].
    /// - <code>Err([LayoutErr::ExceedsMax]\(size, [align_up]\(align,
    ///   [void_ptr::SZ](SizedProps::SZ)\), 1\))</code> if `size`, after rounding up to the
    ///   alignment which results from rounding `align` itself up to
    ///   <code>[void_ptr]::[SZ](SizedProps::SZ)</code>, would exceed [`USIZE_MAX_NO_HIGH_BIT`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use memapi2::prelude::{Layout, SizedProps};
    /// let l = Layout::posix_memalign_compatible_from_size_align(10, 1).unwrap();
    ///
    /// assert!(l.align() >= usize::SZ); // or memapi2::helpers::void_ptr::SZ, libc::uintptr_t::SZ
    /// //                                  if available
    /// assert!(l.size() >= 10);
    /// // on 64-bit systems, l == Layout(size = 10, align = 8).
    /// // 32-bit, l == Layout(size = 10, align = 4)
    /// ```
    pub const fn posix_memalign_compatible_from_size_align(
        size: usize,
        align: usize
    ) -> Result<Layout, LayoutErr> {
        if align == 0 {
            return Err(LayoutErr::ZeroAlign);
        } else if !align.is_power_of_two() {
            return Err(LayoutErr::NonPowerOfTwoAlign(align));
        } else if align > usize::MAX - (void_ptr::SZ - 1) {
            return Err(LayoutErr::CRoundUp(align));
        }
        // SAFETY: see `align_up_checked`.
        Layout::from_size_align(size, unsafe { align_up(align, void_ptr::SZ) })
    }

    /// Creates a layout with the given size and alignment.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `align` is a non-zero power of two.
    /// - `size` is non-zero.
    /// - `size` rounded up to `align` does not exceed [`USIZE_MAX_NO_HIGH_BIT`].
    #[cfg_attr(any(miri, debug_assertions), track_caller)]
    #[must_use]
    #[inline]
    pub const unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Layout {
        assert_unsafe_precondition!(
            "`Layout::from_size_align_unchecked` requires that `align` is a non-zero power of two \
             and `size` rounded up to `align` does not exceed `USIZE_MAX_NO_HIGH_BIT`.",
            (size: usize = size, align: usize = align)
                => [::core::matches!(align_up_checks(size, align), Ok(()))]
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
    /// # Errors
    ///
    /// - <code>Err([LayoutErr::ZeroAlign])</code> if `align == 0`.
    /// - <code>Err([LayoutErr::NonPowerOfTwoAlign]\(align\))</code> if `align` is not a power of
    ///   two.
    /// - <code>Err([LayoutErr::ExceedsMax]\(size, align, 1\))</code> if
    ///   <code>self.[size](Layout::size)()</code> rounded up to the nearest multiple of `align`
    ///   would exceed [`USIZE_MAX_NO_HIGH_BIT`].
    ///
    /// # Example
    ///
    /// ```
    /// # use memapi2::layout::Layout;
    ///
    /// assert_eq!(unsafe { Layout::from_size_align_unchecked(6, 8) }.padding_needed_for(8), Ok(2));
    /// ```
    #[inline]
    pub const fn padding_needed_for(&self, align: usize) -> Result<usize, LayoutErr> {
        let sz = self.size();
        match align_up_checked(sz, align) {
            // align_up_checked guarantees its return value will be >= the input, so new - sz cannot
            // underflow
            Ok(new) => Ok(new - sz),
            Err(e) => Err(e)
        }
    }

    /// Creates a layout by rounding the size of this layout up to a multiple of the layout's
    /// alignment.
    ///
    /// This is equivalent to adding the result of [`Layout::padding_needed_for`] to
    /// [`self.size()`](Layout::size).
    #[must_use]
    #[inline]
    pub const fn pad_to_align(&self) -> Layout {
        // SAFETY: constructors require that the size and alignment are valid for this operation;
        // see `align_up_checked`.
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
    /// <code>Err([LayoutErr::ArithErr])</code> if multiplying `count` by
    ///   <code>layout.[size](Layout::size)()</code>, rounded up to the nearest multiple of
    ///   <code>layout.[align](Layout::align)()</code>, would overflow.
    #[inline]
    pub const fn repeat(&self, count: usize) -> Result<(Layout, usize), LayoutErr> {
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
    /// In other words, if the layout returned by `repeat_packed` is used to allocate an array, it
    /// isn't guaranteed that all elements in the array will be properly aligned.
    ///
    /// Note that this is only `const` on Rust versions 1.47 and above.
    ///
    /// # Errors
    ///
    /// - <code>Err([LayoutErr::ArithErr])</code> if multiplying
    ///   <code>layout.[size](Layout::size)()</code> by `count` would overflow.
    /// - <code>Err([LayoutErr::ExceedsMax]\([self.size()](Layout::size) * count,
    ///   [self.align()](Layout::align), 1\))</code> if <code>[self.size()](Layout::size) *
    ///   count</code> rounded up to the nearest multiple of [`self.align()`](Layout::align) would
    ///   exceed [`USIZE_MAX_NO_HIGH_BIT`].
    #[inline]
    pub const fn repeat_packed(&self, count: usize) -> Result<Layout, LayoutErr> {
        // this is ~1.6x faster than using checked_op
        if count > usize::MAX / self.size() {
            return Err(LayoutErr::ArithErr(ArithErr(self.size(), ArithOp::Mul, count)));
        }
        match Layout::from_size_align(self.size() * count, self.align()) {
            Ok(layout) => Ok(layout),
            Err(e) => Err(e)
        }
    }

    /// Creates a layout with the same size as `self` but an alignment meeting `align`. If
    /// <code>[self.align()](Layout::align) >= align</code>, returns `self`.
    ///
    /// This method doesn't modify the size of the new layout.
    ///
    /// # Errors
    ///
    /// - <code>Err([LayoutErr::ZeroAlign])</code> if `align == 0`.
    /// - <code>Err([LayoutErr::NonPowerOfTwoAlign]\(align\))</code> if `align` is not a power of
    ///   two.
    /// - <code>Err([LayoutErr::ExceedsMax]\([self.size()](Layout::size), align, 1\))</code> if
    ///   [`self.size()`](Layout::size) rounded up to the nearest multiple of `align` would exceed
    ///   [`USIZE_MAX_NO_HIGH_BIT`].
    #[inline]
    pub const fn align_to(&self, align: usize) -> Result<Layout, LayoutErr> {
        if align > self.align() { Layout::from_size_align(self.size(), align) } else { Ok(*self) }
    }

    /// Returns a layout with the same `size` as `self` but whose alignment has been rounded up to
    /// the nearest multiple of `align`.
    ///
    /// This differs from [`Layout::align_to`]: [`align_to`](Layout::align_to) sets the layout's
    /// alignment to the provided alignment if that alignment is larger than the current one.
    /// This method instead rounds [`self.align()`](Layout::align) up to a multiple of the provided
    /// `align`.
    ///
    /// # Errors
    ///
    /// - <code>Err([LayoutErr::ZeroAlign])</code> if `align == 0`.
    /// - <code>Err([LayoutErr::NonPowerOfTwoAlign]\(align\))</code> if `align` is not a power of
    ///   two.
    /// - <code>Err([LayoutErr::ExceedsMax]\([self.size()](Layout::size), align, 1\))</code> if
    ///   [`self.size()`](Layout::size) rounded up to the nearest multiple of the new alignment
    ///   exceeds [`USIZE_MAX_NO_HIGH_BIT`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use memapi2::layout::Layout;
    /// // current alignment 8, round up to a multiple of 16 => next multiple is 16
    /// let l = unsafe { Layout::from_size_align_unchecked(30, 8) };
    /// let rounded = l.align_to_multiple_of(16).unwrap();
    /// assert_eq!(rounded.align(), 16);
    /// assert_eq!(rounded.size(), 30);
    /// ```
    #[inline]
    pub const fn align_to_multiple_of(&self, align: usize) -> Result<Layout, LayoutErr> {
        if align == 0 {
            return Err(LayoutErr::ZeroAlign);
        } else if !align.is_power_of_two() {
            return Err(LayoutErr::NonPowerOfTwoAlign(align));
        }

        let cur_align = self.align();

        if is_multiple_of(cur_align, align) {
            Ok(*self)
        } else {
            let m1 = align - 1;
            if cur_align > usize::MAX - m1 {
                return Err(LayoutErr::ArithErr(ArithErr(cur_align, ArithOp::Add, m1)));
            }
            // SAFETY: see `align_up_checked`.
            Layout::from_size_align(self.size(), unsafe { align_up(cur_align, align) })
        }
    }

    /// Converts this layout into one compatible with C's `posix_memalign` requirements.
    ///
    /// C's `posix_memalign(out, alignment, size)` requires `alignment` is a power of two, non-zero,
    /// and a multiple of <code>[void_ptr]::[SZ](SizedProps::SZ)</code>
    ///
    /// Therefore, the alignment will be rounded up to the nearest multiple of
    /// <code>[void_ptr]::[SZ](SizedProps::SZ)</code> if it isn't already.
    ///
    /// # Errors
    ///
    /// <code>Err([LayoutErr::CRoundUp]\([self.size()](Layout::size), [self.align()](Layout::align),
    /// [LayoutErr::CRoundUp]\))</code> if:
    /// - `align == 0`.
    /// - `align` is not a power of two.
    /// - `align` rounded up to <code>[void_ptr]::[SZ](SizedProps::SZ)</code> would exceed the
    ///   maximum allowed alignment.
    ///
    /// [size_of]: ::core::mem::size_of
    ///
    /// # Examples
    ///
    /// ```
    /// # use memapi2::prelude::{Layout, SizedProps};
    /// let l = Layout::from_size_align(10, 1).unwrap();
    /// let compatible = l.to_posix_memalign_compatible().unwrap();
    ///
    /// assert!(compatible.align() >= usize::SZ); // or memapi2::helpers::void_ptr::SZ,
    /// //                                            libc::uintptr_t::SZ if available
    /// assert!(compatible.size() >= 10);
    /// // on 64-bit systems, compatible == Layout(size = 10, align = 8).
    /// // 32-bit, compatible == Layout(size = 10, align = 4)
    /// ```
    #[inline]
    pub const fn to_posix_memalign_compatible(&self) -> Result<Layout, LayoutErr> {
        if self.align() > usize::MAX - (void_ptr::SZ - 1) {
            return Err(LayoutErr::CRoundUp(self.align()));
        }

        // SAFETY: see `align_up_checked`.
        Layout::from_size_align(self.size(), unsafe { align_up(self.align(), void_ptr::SZ) })
    }

    /// Returns `true` if this layout is zero-sized.
    #[must_use]
    pub const fn is_zsl(&self) -> bool {
        self.size() == 0
    }

    #[cfg(any(not(feature = "no_alloc"), feature = "std"))]
    /// Converts this layout to a [`StdLayout`].
    #[must_use]
    #[inline]
    pub const fn to_stdlib(self) -> StdLayout {
        // SAFETY: we validate all layout's requirements ourselves
        unsafe { StdLayout::from_size_align_unchecked(self.size(), self.align()) }
    }

    #[cfg(any(not(feature = "no_alloc"), feature = "std"))]
    /// Converts a [`StdLayout`] to a [`Layout`].
    ///
    /// Note that this is only `const` on Rust versions 1.50 and above.
    #[::rustversion::attr(since(1.50), const)]
    #[must_use]
    #[inline]
    pub fn from_stdlib(layout: StdLayout) -> Layout {
        // SAFETY: we share layout's requirements.
        unsafe { Layout::from_size_align_unchecked(layout.size(), layout.align()) }
    }
}
