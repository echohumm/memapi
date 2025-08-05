use crate::{
    error::ArithOp,
    helpers::{
        alloc_slice, dealloc_n, layout_or_sz_align, nonnull_slice_from_raw_parts,
        slice_ptr_from_raw_parts, SliceAllocGuard, TRUNC_LGR,
    },
    owned::VariableError::{Hard, Soft},
    type_props::SizedProps,
    Alloc, AllocError, DefaultAlloc,
};
use core::{
    alloc::Layout,
    borrow::{Borrow, BorrowMut},
    cmp::Ordering,
    fmt::{self, Debug, Display, Formatter},
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::{forget, transmute, MaybeUninit},
    ops::{Deref, DerefMut, Index, IndexMut},
    ptr::{self, replace, NonNull},
    slice::{self, SliceIndex},
};
// TODO: more array utilities like into_array, into_flattened() to reverse into_chunks, etc.

/// Calculates the actual size for a buffer, taking into account `T`'s potentially ZST status.
#[inline]
const fn actual_size<T>(sz: usize) -> usize {
    if T::IS_ZST {
        0
    } else {
        sz
    }
}

/// An error which can be soft or hard.
pub enum VariableError<S, H> {
    /// A soft error.
    Soft(S),
    /// A hard error.
    Hard(H),
}

impl<S: Debug, H: Debug> Debug for VariableError<S, H> {
    //noinspection DuplicatedCode
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Soft(s) => write!(f, "Soft error: {:?}", s),
            Hard(h) => write!(f, "Hard error: {:?}", h),
        }
    }
}

impl<S: Display, H: Display> Display for VariableError<S, H> {
    //noinspection DuplicatedCode
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Soft(s) => write!(f, "Soft error: {}", s),
            Hard(h) => write!(f, "Hard error: {}", h),
        }
    }
}

#[cfg(feature = "std")]
impl<S: Display + Debug, H: Display + Debug> std::error::Error for VariableError<S, H> {}

//noinspection RsUnnecessaryQualifications
/// An owned buffer of multiple `T` allocated using `A`.
///
/// This is pretty much a low-level [`Vec`](alloc::vec::Vec), aside from requiring a
/// manual drop via [`drop_and_dealloc`](OwnedBuf::drop_and_dealloc),
/// [`drop_zero_and_dealloc`](OwnedBuf::drop_zero_and_dealloc), [`reset`](OwnedBuf::reset), or
/// [`reset_zero`](OwnedBuf::reset_zero).
///
/// The drop functions consume, while the reset functions do not.
pub struct OwnedBuf<T, A: Alloc = DefaultAlloc> {
    /// The buffer.
    buf: NonNull<T>,
    /// The number of initialized elements.
    init: usize,
    /// The length of the entire buffer.
    size: usize,
    /// The allocator.
    alloc: A,
    _marker: PhantomData<T>,
}

impl<T> OwnedBuf<T> {
    /// Creates a new owned buffer of `T` with the given length, in the default allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn new(len: usize) -> Result<OwnedBuf<T>, AllocError> {
        OwnedBuf::new_in(len, DefaultAlloc)
    }

    const_if! {
        "extra_const",
        "Creates a new, unallocated owned buffer of `T`, set to use the default allocator for \
        future allocations.",
        #[must_use]
        #[inline]
        pub const fn new_unallocated() -> OwnedBuf<T> {
            OwnedBuf::new_unallocated_in(DefaultAlloc)
        }
    }
}

impl<T, A: Alloc> OwnedBuf<T, A> {
    /// Creates a new owned buffer of `T` with the given length, in the given allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn new_in(len: usize, alloc: A) -> Result<OwnedBuf<T, A>, AllocError> {
        Ok(OwnedBuf {
            buf: if T::IS_ZST {
                NonNull::dangling()
            } else {
                alloc_slice::<T, A>(&alloc, len, A::alloc)?.cast()
            },
            init: 0,
            size: len,
            alloc,
            _marker: PhantomData,
        })
    }

    const_if! {
        "extra_const",
        "Creates a new, unallocated owned buffer of `T`, set to use the given allocator for future \
        allocations.",
        #[must_use]
        #[inline]
        pub const fn new_unallocated_in(alloc: A) -> OwnedBuf<T, A> {
            OwnedBuf {
                buf: NonNull::dangling(),
                init: 0,
                size: 0,
                alloc,
                _marker: PhantomData,
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Breaks the owned buffer into its raw data.",
        pub const fn into_raw_parts(self) -> (NonNull<T>, usize, usize, A) {
            let out = (self.buf, self.init, self.size, unsafe {
                #[allow(clippy::borrow_as_ptr)]
                ptr::read(&self.alloc as *const A)
            });
            forget(self);
            out
        }
    }

    const_if! {
        "extra_const",
        "Creates a new owned buffer of `T` from the given parts.\n\n# Safety\n\nThe caller must \
        ensure `buf` points to a valid buffer of `init` count initialized `T` and a capacity of \
        `size`, allocated using `alloc`.",
        #[must_use]
        #[inline]
        pub const unsafe fn from_raw_parts(
            buf: NonNull<T>,
            init: usize,
            size: usize,
            alloc: A,
        ) -> OwnedBuf<T, A> {
            OwnedBuf {
                buf,
                init,
                size: actual_size::<T>(size),
                alloc,
                _marker: PhantomData,
            }
        }
    }

    const_if! {
        "extra_const",
        "Returns the total number of elements in the buffer.",
        #[inline]
        pub const fn size(&self) -> usize {
            if T::IS_ZST {
                usize::MAX
            } else {
                self.size
            }
        }
    }

    const_if! {
        "extra_const",
        "Returns the number of initialized elements in the buffer.",
        #[inline]
        pub const fn initialized(&self) -> usize {
            self.init
        }
    }

    const_if! {
        "extra_extra_const",
        "Sets the initialized element count.\n\n# Safety\n\nAll elements up to `init` elements \
        must be guaranteed to be initialized before use.",
        #[inline]
        pub const unsafe fn set_initialized(&mut self, init: usize) {
            self.init = init;
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to the contained allocator.",
        #[inline]
        pub const fn alloc(&self) -> &A {
            &self.alloc
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to the contained allocator.",
        #[inline]
        pub const fn alloc_mut(&mut self) -> &mut A {
            &mut self.alloc
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the entire buffer.",
        #[inline]
        pub const fn buf_ptr(&self) -> NonNull<[MaybeUninit<T>]> {
            nonnull_slice_from_raw_parts(self.buf.cast::<MaybeUninit<T>>(), self.size)
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the initialized portion of the buffer.",
        #[inline]
        pub const fn init_buf_ptr(&self) -> NonNull<[T]> {
            nonnull_slice_from_raw_parts(self.buf.cast::<T>(), self.init)
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the uninitialized portion of the buffer.",
        #[inline]
        pub const fn uninit_buf_ptr(&self) -> NonNull<[MaybeUninit<T>]> {
            nonnull_slice_from_raw_parts(
                unsafe {
                    NonNull::new_unchecked(
                        self.buf.as_ptr().add(self.init).cast::<MaybeUninit<T>>()
                    )
                },
                self.size - self.init,
            )
        }
    }

    const_if! {
        "extra_const",
        "Gets a slice of the entire buffer.",
        #[inline]
        pub const fn buf(&self) -> &[MaybeUninit<T>] {
            unsafe { &*(self.buf_ptr().as_ptr() as *const [MaybeUninit<T>]) }
        }
    }

    const_if! {
        "extra_const",
        "Gets a slice of the initialized portion of the buffer.",
        #[inline]
        pub const fn init_buf(&self) -> &[T] {
            unsafe { &*(self.init_buf_ptr().as_ptr() as *const [T]) }
        }
    }

    const_if! {
        "extra_const",
        "Gets a slice of the uninitialized portion of the buffer.",
        #[inline]
        pub const fn uninit_buf(&self) -> &[MaybeUninit<T>] {
            unsafe { &*(self.uninit_buf_ptr().as_ptr() as *const [MaybeUninit<T>]) }
        }
    }

    const_if! {
        "extra_extra_const",
         "Gets a mutable slice of the entire buffer.",
        #[inline]
        pub const fn buf_mut(&mut self) -> &mut [MaybeUninit<T>] {
            unsafe { &mut *self.buf_ptr().as_ptr() }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable slice of the initialized portion of the buffer.",
        #[inline]
        pub const fn init_buf_mut(&mut self) -> &mut [T] {
            unsafe { &mut *self.init_buf_ptr().as_ptr() }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable slice of the uninitialized portion of the buffer.",
        #[inline]
        pub const fn uninit_buf_mut(&mut self) -> &mut [MaybeUninit<T>] {
            unsafe { &mut *self.uninit_buf_ptr().as_ptr() }
        }
    }

    const_if! {
        "extra_extra_const",
        "Attempts to initialize the next element.\n\n# Errors\n\nReturns `Err(val)` if at \
        capacity.",
        #[inline]
        pub const fn try_init_next(&mut self, val: T) -> Result<(), T> {
            if self.init == self.size {
                return Err(val);
            }

            unsafe {
                self.init_next_unchecked(val);
            }
            Ok(())
        }
    }

    /// Initializes the next element, growing the buffer if necessary.
    ///
    /// # Errors
    ///
    /// If growth was necessary:
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[inline]
    pub fn init_next_grow(&mut self, val: T) -> Result<(), AllocError> {
        self.expand_to_fit(self.init + 1)?;
        unsafe {
            self.init_next_unchecked(val);
        }
        Ok(())
    }

    const_if! {
        "extra_extra_const",
        "Initializes the next element without checking for space.\n\n# Safety\n\nThe caller must \
        ensure `self.init < self.size`",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const unsafe fn init_next_unchecked(&mut self, val: T) {
            ptr::write(self.buf.as_ptr().add(self.init), val);
            self.init += 1;
        }
    }

    const_if! {
        "extra_extra_const",
        "Removes and returns the last element from the initialized portion of the buffer if it \
        exists.",
        #[inline]
        pub const fn remove_last(&mut self) -> Option<T> {
            if self.init != 0 {
                Some(unsafe { self.remove_last_unchecked() })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Removes and returns the last element from the initialized portion of the buffer.\n\n# \
        Safety\n\nThe caller must ensure there is an initialized element to remove.",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const unsafe fn remove_last_unchecked(&mut self) -> T {
            self.init -= 1;
            ptr::read(self.buf.as_ptr().add(self.init))
        }
    }

    const_if! {
        "extra_extra_const",
        "Removes and returns the element at the given index from the initialized portion of the \
        buffer if it exists.",
        #[inline]
        pub const fn remove(&mut self, idx: usize) -> Option<T> {
            if idx < self.init {
                Some(unsafe { self.remove_unchecked(idx) })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Removes and returns the element at the given index.\n\n# Safety\n\nThe caller must ensure \
        the index is in the bounds of the initialized buffer.",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const unsafe fn remove_unchecked(&mut self, idx: usize) -> T {
            let src = self.get_ptr_unchecked(idx);
            let value = ptr::read(src.as_ptr());
            ptr::copy(src.as_ptr().add(1), src.as_ptr(), self.init - idx - 1);
            self.init -= 1;
            value
        }
    }

    const_if! {
        "extra_extra_const",
        "Replaces the last element of the initialized portion of the buffer.\n\n# Errors\n\nReturns
        `Err(val)` if the buffer is empty. Otherwise, returns `Ok(replaced_val)`.",
        #[inline]
        pub const fn replace_last(&mut self, val: T) -> Result<T, T> {
            self.replace(self.init - 1, val)
        }
    }

    const_if! {
        "extra_extra_const",
        "Replaces the element at the given index from the initialized portion of the buffer.\n\n# \
        Errors\n\nReturns `Err(val)` if the index is out of bounds. Otherwise, returns \
        `Ok(replaced_val)`.",
        #[inline]
        pub const fn replace(&mut self, idx: usize, val: T) -> Result<T, T> {
            if idx <= self.init {
                Ok(unsafe { replace(self.get_ptr_unchecked(idx).as_ptr(), val) })
            } else {
                Err(val)
            }
        }
    }

    /// Attempts to insert `val` at the given `idx`, growing if necessary.
    ///
    /// # Errors
    ///
    /// - `Err(Soft(val))` if the index is out of bounds.
    /// - `Err(Hard((alloc_err, val)))` if the index is in bounds, but the vector is full and
    ///   allocation for an expansion fails.
    ///
    /// `alloc_err` may be:
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    pub fn try_insert_grow(
        &mut self,
        idx: usize,
        val: T,
    ) -> Result<(), VariableError<T, (T, AllocError)>> {
        if idx > self.init {
            return Err(Soft(val));
        }
        if let Err(e) = self.expand_to_fit(self.init + 1) {
            return Err(Hard((val, e)));
        }

        unsafe {
            self.insert_unchecked(idx, val);
        }

        Ok(())
    }

    const_if! {
        "extra_extra_const",
        "Attempts to insert `val` at the given `idx`.\n\n# Errors\n\n- `Err(val)` if the index is \
        out of bounds, or there is no space for the element.",
        pub const fn try_insert(&mut self, idx: usize, val: T) -> Result<(), T> {
            if idx > self.init || self.init == self.size {
                return Err(val);
            }

            unsafe {
                self.insert_unchecked(idx, val);
            }

            Ok(())
        }
    }

    const_if! {
        "extra_extra_const",
        "Inserts `val` at the given `idx`.\n\n# Safety\n\nThe caller must ensure `idx` is in \
        bounds and there is space for a new element.",
        #[cfg_attr(miri, track_caller)]
        pub const unsafe fn insert_unchecked(&mut self, idx: usize, val: T) {
            let dst = self.get_ptr_unchecked(idx);
            if idx != self.init {
                ptr::copy_nonoverlapping(dst.as_ptr(), dst.as_ptr().add(1), self.init - idx);
            }
            ptr::write(dst.as_ptr(), val);
            self.init += 1;
        }
    }

    // TODO: finish docs

    /// Placeholder docs
    pub fn try_init_next_slice_grow<'s>(
        &mut self,
        slice: &'s [T],
    ) -> Result<(), VariableError<&'s [T], (&'s [T], AllocError)>>
    where
        T: Clone,
    {
        self.expand_to_fit(self.init + slice.len())
            .map_err(|e| Hard((slice, e)))?;
        unsafe {
            self.init_next_slice_unchecked(slice);
        }
        Ok(())
    }

    /// Placeholder docs
    pub fn try_init_next_slice<'s>(&mut self, slice: &'s [T]) -> Result<(), &'s [T]>
    where
        T: Clone,
    {
        if self.init + slice.len() > self.size {
            return Err(slice);
        }

        unsafe {
            self.init_next_slice_unchecked(slice);
        }
        Ok(())
    }

    /// Placeholder docs
    pub unsafe fn init_next_slice_unchecked(&mut self, slice: &[T])
    where
        T: Clone,
    {
        <[T] as SpecInitNextSlice<T, A>>::init_next_slice(self, slice);
    }

    /// Placeholder docs
    #[allow(clippy::missing_errors_doc)]
    #[allow(clippy::type_complexity)]
    pub fn replace_last_slice<'s, A2: Alloc>(
        &mut self,
        new_slice: &'s [T],
        out_alloc: A2,
    ) -> Result<OwnedBuf<T, A2>, VariableError<(&'s [T], A2), ((&'s [T], A2), AllocError)>> {
        self.replace_slice(
            match self.init.checked_sub(new_slice.len()) {
                Some(idx) => idx,
                None => {
                    return Err(Hard((
                        (new_slice, out_alloc),
                        // TODO: more consistently use checked ops and this error. maybe make a
                        //  macro or some helpers?
                        AllocError::ArithmeticOverflow(self.init, ArithOp::Sub, new_slice.len()),
                    )));
                }
            },
            new_slice,
            out_alloc,
        )
    }

    // TODO: make sure all slice methods are still correct now that they use normal slices
    // TODO: make sure all const methods don't return stuff with tuples or variable errors, as
    //  them not being Destruct causes problems.

    /// Placeholder docs
    #[allow(clippy::missing_errors_doc)]
    #[allow(clippy::type_complexity)]
    pub fn replace_slice<'s, A2: Alloc>(
        &mut self,
        idx: usize,
        new_slice: &'s [T],
        out_alloc: A2,
    ) -> Result<OwnedBuf<T, A2>, VariableError<(&'s [T], A2), ((&'s [T], A2), AllocError)>> {
        let cnt = new_slice.len();
        // must replace in the initialized region (or 1 outside it, which is basically extending)
        if idx > self.init {
            return Err(Soft((new_slice, out_alloc)));
        }
        // get the number of elements we’ll be swapping out
        let overlap_cnt = self.init - idx;
        // new initialized length after the replacement (accounting for overlap and growth)
        let new_init = idx + cnt - overlap_cnt;

        // grow if needed
        if let Err(e) = self.expand_to_fit(new_init) {
            return Err(Hard(((new_slice, out_alloc), e)));
        }

        // get the region we’re about to overwrite
        let init_elems = match self.get_slice_mut(idx, overlap_cnt) {
            Some(buf) => buf,
            None => return Err(Soft((new_slice, out_alloc))),
        };

        // allocate space for the removed elements
        let out_buf = match alloc_slice::<T, A2>(&out_alloc, overlap_cnt, A2::alloc) {
            Ok(mem) => mem.cast::<T>(),
            Err(e) => return Err(Hard(((new_slice, out_alloc), e))),
        };

        // copy the old elements out
        unsafe {
            ptr::copy_nonoverlapping(init_elems.as_ptr(), out_buf.as_ptr(), overlap_cnt);
        }

        unsafe {
            // overwrite with new elements
            ptr::copy_nonoverlapping(new_slice.as_ptr(), self.buf.as_ptr().add(idx), cnt);

            self.init = new_init;

            Ok(OwnedBuf::from_raw_parts(
                out_buf,
                overlap_cnt,
                overlap_cnt,
                out_alloc,
            ))
        }
    }

    #[allow(clippy::type_complexity)]
    /// Attempts to insert `slice` at `idx`, growing if necessary.
    ///
    /// # Errors
    ///
    /// - `Err(Soft(slice))` if the index is out of bounds.
    /// - `Err(Hard((alloc_err, slice)))` if the index is in bounds, but the vector needs more space
    ///   and allocation for an expansion fails.
    ///
    /// `alloc_err` may be:
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    pub fn try_insert_slice_grow<'s>(
        &mut self,
        idx: usize,
        new_slice: &'s [T],
    ) -> Result<(), VariableError<&'s [T], (&'s [T], AllocError)>> {
        if idx > self.init {
            return Err(Soft(new_slice));
        }
        if let Err(e) = self.expand_to_fit(self.init + new_slice.len()) {
            return Err(Hard((new_slice, e)));
        }

        unsafe {
            self.insert_slice_unchecked(idx, new_slice);
        }

        Ok(())
    }

    /// Attempts to insert `slice` at the given `idx`.
    ///
    /// # Errors
    ///
    /// - `Err(slice)` if the index is out of bounds, or there is no space for some elements of the
    ///   slice.
    pub fn try_insert_slice<'s>(&mut self, idx: usize, new_slice: &'s [T]) -> Result<(), &'s [T]> {
        if idx > self.init || self.init + new_slice.len() > self.size {
            return Err(new_slice);
        }

        unsafe {
            self.insert_slice_unchecked(idx, new_slice);
        }

        Ok(())
    }

    /// Inserts `slice` at the given `idx`.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - the index is in bounds
    /// - the index plus the initialized length of the slice will not go outside of the allocated
    ///   buffer.
    pub unsafe fn insert_slice_unchecked(&mut self, idx: usize, new_slice: &[T]) {
        // destination of the slice
        let dst = self.get_ptr_unchecked(idx);
        // length of the slice
        let len = new_slice.len();
        // shift elements over to make space as necessary
        if idx != self.init {
            ptr::copy_nonoverlapping(dst.as_ptr(), dst.as_ptr().add(len), self.init - idx);
        }
        // pointer to initialized elements
        let src = new_slice.as_ptr();
        // write in the elements
        ptr::copy_nonoverlapping(src, self.buf.as_ptr().add(idx), len);
        // update initialized element count
        self.init += len;
    }

    /// Removes exactly `len` elements from this buffer, starting at `idx`, and returns them in a
    /// new [`OwnedBuf`] with the same allocator (cloned).
    ///
    /// # Returns
    ///
    /// - `Some(Ok(buf))` if `idx + len` is within bounds, and allocation for the returned buffer
    ///   succeeds.
    /// - `Some(Err(alloc_err))` if allocation for the returned buffer fails.
    /// - `None` if `idx + len` exceeds the number of initialized elements.
    ///
    /// `alloc_err` may be:
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    pub fn remove_slice(
        &mut self,
        idx: usize,
        len: usize,
    ) -> Option<Result<OwnedBuf<T, A>, AllocError>>
    where
        A: Clone,
    {
        if idx + len >= self.init {
            return None;
        }

        Some(unsafe { self.remove_slice_unchecked(idx, len) })
    }

    /// Removes up to `req_len` elements from this buffer, starting at `idx`, and returns them in a
    /// new [`OwnedBuf`] with the same allocator (cloned).
    ///
    /// # Returns
    ///
    /// - `Some(Ok(buf))` if `idx + len` is within bounds, and allocation for the returned buffer
    ///   succeeds. `buf`'s length and size will be as many elements were available, up to
    ///   `req_len`.
    /// - `Some(Err(alloc_err))` if allocation for the returned buffer fails.
    /// - `None` if `idx` is out of bounds, and thus so is every element.
    ///
    /// `alloc_err` may be:
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    pub fn remove_slice_to(
        &mut self,
        idx: usize,
        req_len: usize,
    ) -> Option<Result<OwnedBuf<T, A>, AllocError>>
    where
        A: Clone,
    {
        if idx >= self.init {
            return None;
        }
        let len = req_len.min(self.init - idx);

        Some(unsafe { self.remove_slice_unchecked(idx, len) })
    }

    /// Removes exactly `len` elements from this buffer, starting at `idx`, and returns them in a
    /// new [`OwnedBuf`] with the same allocator (cloned).
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the slice is entirely in bounds.
    pub unsafe fn remove_slice_unchecked(
        &mut self,
        idx: usize,
        len: usize,
    ) -> Result<OwnedBuf<T, A>, AllocError>
    where
        A: Clone,
    {
        let mut new_buf = OwnedBuf::<T, A>::new_in(len, self.alloc.clone())?;
        for i in 0..len {
            new_buf.init_next_unchecked(ptr::read(self.get_ptr_unchecked(idx + i).as_ptr()));
        }
        if idx + len < self.init {
            self.init -= len;
            ptr::copy(
                self.buf.as_ptr().add(idx + len),
                self.buf.as_ptr().add(idx),
                self.init - idx,
            );
        }
        Ok(new_buf)
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the element at the given `idx` if it is initialized.",
        #[inline]
        pub const fn get_ptr(&self, idx: usize) -> Option<NonNull<T>> {
            if idx < self.init {
                Some(unsafe { self.get_ptr_unchecked(idx) })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to the element at the given `idx` if it is initialized.",
        #[inline]
        pub const fn get(&self, idx: usize) -> Option<&T> {
            if idx < self.init {
                Some(unsafe { self.get_unchecked(idx) })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to the element at the given `idx` if it is initialized.",
        #[inline]
        pub const fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
            if idx < self.init {
                Some(unsafe { self.get_mut_unchecked(idx) })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the uninitialized element at the given `idx` if it exists.",
        #[inline]
        pub const fn get_uninit_ptr(&self, idx: usize) -> Option<NonNull<MaybeUninit<T>>> {
            if idx < self.size {
                Some(unsafe { self.get_ptr_unchecked(idx).cast() })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to the uninitialized element at the given `idx` if it exists.",
        #[inline]
        pub const fn get_uninit(&self, idx: usize) -> Option<&MaybeUninit<T>> {
            if idx < self.size {
                Some(unsafe {
                    &*(self.get_ptr_unchecked(idx).cast().as_ptr() as *const MaybeUninit<T>)
                })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to the uninitialized element at the given `idx` if it exists.",
        #[inline]
        pub const fn get_uninit_mut(&mut self, idx: usize) -> Option<&mut MaybeUninit<T>> {
            if idx < self.size {
                Some(unsafe { &mut *self.get_ptr_unchecked(idx).cast().as_ptr() })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the element at the given `idx` if it is initialized, or a pointer to \
        the initialized element if it exists.\n\n# Errors\n\n- `Err(None)` if the index is \
        entirely out of bounds.\n- `Err(Some(uninit_ptr))` if the index is out of the initialized \
        buffer, but still in the buffer.",
        #[inline]
        pub const fn try_get_ptr(
            &self,
            idx: usize,
        ) -> Result<NonNull<T>, Option<NonNull<MaybeUninit<T>>>> {
            if idx < self.init {
                Ok(unsafe { self.get_ptr_unchecked(idx) })
            } else {
                Err(self.get_uninit_ptr(idx))
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to the element at the given `idx` if it is initialized, or a reference \
        to the initialized element if it exists.\n\n# Errors\n\n- `Err(None)` if the index is \
        entirely out of bounds.\n- `Err(Some(uninit_ref))` if the index is out of the initialized \
        buffer, but still in the buffer.",
        #[inline]
        pub const fn try_get(&self, idx: usize) -> Result<&T, Option<&MaybeUninit<T>>> {
            if idx < self.init {
                Ok(unsafe { self.get_unchecked(idx) })
            } else {
                Err(self.get_uninit(idx))
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to the element at the given `idx` if it is initialized, or a \
        mutable reference to the uninitialized element if it exists.\n\n# Errors\n\n- `Err(None)` \
        if the index is entirely out of bounds.\n- `Err(Some(uninit_ptr))` if the index is out of \
        the initialized buffer, but still in the buffer.",
        #[inline]
        pub const fn try_get_mut(&mut self, idx: usize)
        -> Result<&mut T, Option<&mut MaybeUninit<T>>> {
            if idx < self.init {
                Ok(unsafe { self.get_mut_unchecked(idx) })
            } else {
                Err(self.get_uninit_mut(idx))
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the element at the given `idx`.\n\n# Safety\n\nThe caller must ensure \
        the index is in bounds.",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const unsafe fn get_ptr_unchecked(&self, idx: usize) -> NonNull<T> {
            NonNull::new_unchecked(self.buf.as_ptr().add(idx))
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to the element at the given `idx`.\n\n# Safety\n\nThe caller must ensure \
        the index is in bounds.",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const unsafe fn get_unchecked(&self, idx: usize) -> &T {
            &*(self.get_ptr_unchecked(idx).as_ptr() as *const T)
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to the element at the given `idx`.\n\n# Safety\n\nThe caller \
        must ensure the index is in bounds.",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const unsafe fn get_mut_unchecked(&mut self, idx: usize) -> &mut T {
            &mut *self.get_ptr_unchecked(idx).as_ptr()
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to a portion of the initialized buffer if the parameters are in bounds.",
        #[inline]
        pub const fn get_slice_ptr(&self, start: usize, len: usize) -> Option<NonNull<[T]>> {
            if start + len < self.init {
                Some(unsafe { self.get_slice_ptr_unchecked(start, len) })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to a portion of the initialized buffer if the parameters are in bounds.",
        #[inline]
        pub const fn get_slice(&self, start: usize, len: usize) -> Option<&[T]> {
            if start + len < self.init {
                Some(unsafe { self.get_slice_unchecked(start, len) })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to a portion of the initialized buffer if the parameters are in \
        bounds.",
         #[inline]
         pub const fn get_slice_mut(&mut self, start: usize, len: usize) -> Option<&mut [T]> {
             if start + len < self.init {
                 Some(unsafe { self.get_slice_mut_unchecked(start, len) })
             } else {
                 None
             }
         }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to a portion of the buffer if the parameters are in bounds.",
        #[inline]
        pub const fn get_uninit_slice_ptr(
            &self,
            start: usize,
            len: usize,
        ) -> Option<NonNull<[MaybeUninit<T>]>> {
            if start + len < self.size {
                Some(unsafe {
                    transmute::<NonNull<[T]>, NonNull<[MaybeUninit<T>]>>(
                        self.get_slice_ptr_unchecked(start, len),
                    )
                })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to a portion of the buffer if the parameters are in bounds.",
        #[inline]
        pub const fn get_uninit_slice(&self, start: usize, len: usize) -> Option<&[MaybeUninit<T>]>
        {
            if start + len < self.size {
                Some(unsafe {
                    &*(self.get_slice_ptr_unchecked(start, len).as_ptr() as *const [MaybeUninit<T>])
                })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to a portion of the buffer if the parameters are in bounds.",
        #[inline]
        pub const fn get_uninit_slice_mut(
            &mut self,
            start: usize,
            len: usize,
        ) -> Option<&mut [MaybeUninit<T>]> {
            if start + len < self.size {
                Some(unsafe {
                    &mut *(
                        self.get_slice_ptr_unchecked(start, len)
                            .as_ptr() as *mut [MaybeUninit<T>]
                    )
                })
            } else {
                None
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to a portion of the initialized buffer if in bounds, or a pointer to a \
        portion of the buffer if not.\n\n# Errors\n\n- `Err(None)` if the index is entirely out of \
        bounds.\n- `Err(Some(uninit_ptr))` if the index is out of the initialized buffer, but \
        still in the buffer.",
        #[allow(clippy::type_complexity)]
        #[inline]
        pub const fn try_get_slice_ptr(
            &self,
            start: usize,
            len: usize,
        ) -> Result<NonNull<[T]>, Option<NonNull<[MaybeUninit<T>]>>> {
            if start + len < self.init {
                Ok(unsafe { self.get_slice_ptr_unchecked(start, len) })
            } else {
                Err(self.get_uninit_slice_ptr(start, len))
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to a portion of the buffer if in bounds, or a reference to a portion of \
        the buffer if not.\n\n# Errors\n\n- `Err(None)` if the index is entirely out of bounds.\n- \
        `Err(Some(uninit_ref))` if the index is out of the initialized buffer, but still in the \
        buffer.",
        #[inline]
        pub const fn try_get_slice(
            &self,
            start: usize,
            len: usize,
        ) -> Result<&[T], Option<&[MaybeUninit<T>]>> {
            if start + len < self.init {
                Ok(unsafe { self.get_slice_unchecked(start, len) })
            } else {
                Err(self.get_uninit_slice(start, len))
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to a portion of the initialized buffer if in bounds, or a \
        mutable reference to a portion of the buffer if not.\n\n# Errors\n\n- `Err(None)` if the \
        index is entirely out of bounds.\n- `Err(Some(uninit_mut))` if the index is out of the \
        initialized buffer, but still in the buffer.",
        #[inline]
        pub const fn try_get_slice_mut(
            &mut self,
            start: usize,
            len: usize,
        ) -> Result<&mut [T], Option<&mut [MaybeUninit<T>]>> {
            if start + len < self.init {
                Ok(unsafe { self.get_slice_mut_unchecked(start, len) })
            } else {
                Err(self.get_uninit_slice_mut(start, len))
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to a portion of the buffer.\n\n# Safety\n\nThe caller must ensure the \
        parameters are in bounds, meaning:\n- If using the slice as initialized data, \
        `start + len < self.init`\n- If using the slice as uninitialized data, `start + len < \
        self.size`",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const unsafe fn get_slice_ptr_unchecked(&self, start: usize, len: usize) -> NonNull<[T]>
        {
            nonnull_slice_from_raw_parts(self.get_ptr_unchecked(start), len)
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to a portion of the buffer.\n\n# Safety\n\nThe caller must ensure the \
        parameters are in bounds, meaning:\n- If using the slice as initialized data, \
        `start + len < self.init`\n- If using the slice as uninitialized data, `start + len < \
        self.size`",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const unsafe fn get_slice_unchecked(&self, start: usize, len: usize) -> &[T] {
            &*(self.get_slice_ptr_unchecked(start, len).as_ptr() as *const [T])
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to a portion of the buffer.\n\n# Safety\n\nThe caller must \
        ensure the parameters are in bounds, meaning:\n- If using the slice as initialized data, \
        `start + len < self.init`.\n- If using the slice as uninitialized data, `start + len < \
        self.size`.",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const unsafe fn get_slice_mut_unchecked(&mut self, start: usize, len: usize) -> &mut [T]
        {
            &mut *self.get_slice_ptr_unchecked(start, len).as_ptr()
        }
    }

    /// Reserves space for `additional` elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn reserve(&mut self, additional: usize) -> Result<(), AllocError> {
        unsafe {
            self.set_size_unchecked(self.size + additional)?;
        }
        Ok(())
    }

    /// Truncates the buffer down to a new length, dropping any removed elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::Other("attempted to truncate a slice to a larger size")`] if
    ///   `len > self.initialized()`.
    pub fn truncate(&mut self, len: usize) -> Result<(), AllocError> {
        match len.cmp(&self.init) {
            Ordering::Greater => return Err(AllocError::Other(TRUNC_LGR)),
            Ordering::Equal => unsafe {
                ptr::drop_in_place(slice_ptr_from_raw_parts(
                    self.as_mut_ptr().add(len),
                    self.init - len,
                ));
                self.init = len;
            },
            Ordering::Less => {}
        }

        Ok(())
    }

    /// Shrinks the vector's capacity to fit only as many elements as it has.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn shrink_to_fit(&mut self) -> Result<(), AllocError> {
        if self.init < self.size {
            self.buf = unsafe {
                self.alloc
                    .shrink(
                        self.buf.cast::<u8>(),
                        // we were able to allocate with this earlier, so it is valid.
                        Layout::from_size_align_unchecked(self.size * T::SZ, T::ALIGN),
                        Layout::from_size_align_unchecked(self.init * T::SZ, T::ALIGN),
                    )?
                    .cast::<T>()
            };
            self.size = self.init;
        }
        Ok(())
    }

    /// Expands the buffer to `necessary_size`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn expand_to_fit(&mut self, necessary_size: usize) -> Result<(), AllocError> {
        if self.size < necessary_size {
            unsafe {
                self.set_size_unchecked(necessary_size)?;
            }
        }
        Ok(())
    }

    /// Sets the size of the buffer to `new_size`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `self.init <= new_size`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub unsafe fn set_size_unchecked(&mut self, new_size: usize) -> Result<(), AllocError> {
        if new_size == self.size {
            return Ok(());
        } else if T::IS_ZST {
            self.size = new_size;
            return Ok(());
        }
        let layout = layout_or_sz_align::<T>(new_size)
            .map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        let new_buf = self.alloc.alloc(layout)?.cast();
        if self.size != 0 {
            ptr::copy_nonoverlapping(self.buf.as_ptr(), new_buf.as_ptr(), self.init);
            dealloc_n(self.alloc(), self.buf, self.size);
        }
        self.buf = new_buf;
        self.size = new_size;
        Ok(())
    }

    /// Drops all initialized values and resets the count.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn clear(&mut self) {
        self.init = 0;
        self.clear_inner();
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn clear_inner(&self) {
        unsafe {
            ptr::drop_in_place(slice_ptr_from_raw_parts(self.buf.as_ptr(), self.init));
        }
    }

    /// Destructor to drop all initialized elements and deallocate the buffer.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn drop_and_dealloc(self) {
        if self.size != 0 {
            unsafe {
                self.clear_inner();
                dealloc_n(self.alloc(), self.buf, self.size);
            }
            #[cfg(any(feature = "drop_for_owned", feature = "zero_drop_for_owned"))]
            forget(self);
        }
    }

    /// Destructor to drop all initialized elements, zero the allocated memory, and deallocate the
    /// buffer.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn drop_zero_and_dealloc(self) {
        if self.size != 0 {
            unsafe {
                self.drop_zero_nc();
            }
            #[cfg(any(feature = "drop_for_owned", feature = "zero_drop_for_owned"))]
            forget(self);
        }
    }

    /// Drops all initialized elements and deallocates the buffer.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn reset(&mut self) {
        if self.size != 0 {
            unsafe {
                self.clear_inner();
                dealloc_n(self.alloc(), self.buf, self.size);
                self.uninit_values();
            }
        }
    }

    /// Drops all initialized elements, zeroes allocated memory, and deallocates the buffer.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn reset_zero(&mut self) {
        if self.size != 0 {
            unsafe {
                self.drop_zero_nc();
                self.uninit_values();
            }
        }
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn drop_zero_nc(&self) {
        self.clear_inner();
        ptr::write_bytes(self.buf.as_ptr(), 0, self.size);
        dealloc_n(self.alloc(), self.buf, self.size);
    }

    #[inline]
    unsafe fn uninit_values(&mut self) {
        self.init = 0;
        self.size = 0;
        self.buf = NonNull::dangling();
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the initialized portion of the buffer.",
        #[inline]
        pub const fn as_slice_ptr(&self) -> NonNull<[T]> {
            nonnull_slice_from_raw_parts(self.buf, self.init)
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to the initialized portion of the buffer.",
        #[inline]
        pub const fn as_slice(&self) -> &[T] {
            unsafe { &*(nonnull_slice_from_raw_parts(self.buf, self.init).as_ptr() as *const [T]) }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to the initialized portion of the buffer.",
        #[inline]
        pub const fn as_slice_mut(&mut self) -> &mut [T] {
            unsafe { &mut *nonnull_slice_from_raw_parts(self.buf, self.init).as_ptr() }
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the entire buffer.",
        #[inline]
        pub const fn as_uninit_slice_ptr(&self) -> NonNull<[MaybeUninit<T>]> {
            nonnull_slice_from_raw_parts(self.buf.cast::<MaybeUninit<T>>(), self.size)
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to the entire buffer.",
        #[inline]
        pub const fn as_uninit_slice(&self) -> &[MaybeUninit<T>] {
            unsafe {
                &*(
                    nonnull_slice_from_raw_parts(self.buf.cast::<MaybeUninit<T>>(), self.size)
                        .as_ptr() as *const [MaybeUninit<T>]
                )
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to the entire buffer.",
        #[inline]
        pub const fn as_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<T>] {
            unsafe {
                &mut *nonnull_slice_from_raw_parts(self.buf.cast::<MaybeUninit<T>>(), self.size)
                    .as_ptr()
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the initialized portion of the buffer if it exists. Otherwise, gets an \
        uninitialized pointer to the entire buffer.\n\n# Errors\n\nReturns `Err(uninit_ptr)` if \
        there are no initialized elements in the buffer.",
        #[inline]
        #[allow(clippy::type_complexity)]
        pub const fn try_as_slice_ptr(
            &self,
        ) -> Result<NonNull<[T]>, Option<NonNull<[MaybeUninit<T>]>>> {
            if self.init != 0 {
                Ok(self.as_slice_ptr())
            } else if self.size != 0 {
                Err(Some(self.as_uninit_slice_ptr()))
            } else {
                Err(None)
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to the entire buffer if it exists. Otherwise, gets an uninitialized \
        reference to the entire buffer.\n\n# Errors\n\nReturns `Err(uninit_ptr)` if there are no \
        initialized elements in the buffer.",
        #[inline]
        pub const fn try_as_slice(&self) -> Result<&[T], Option<&[MaybeUninit<T>]>> {
            if self.init != 0 {
                Ok(self.as_slice())
            } else if self.size != 0 {
                Err(Some(self.as_uninit_slice()))
            } else {
                Err(None)
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a mutable reference to the initialized portion of the buffer if it exists. \
        Otherwise, gets an uninitialized mutable reference to the entire buffer.\n\n# \
        Errors\n\nReturns `Err(uninit_ptr)` if there are no initialized elements in the buffer.",
        #[inline]
        pub const fn try_as_slice_mut(&mut self) -> Result<&mut [T], Option<&mut [MaybeUninit<T>]>>
        {
            if self.init != 0 {
                Ok(self.as_slice_mut())
            } else if self.size != 0 {
                Err(Some(self.as_uninit_slice_mut()))
            } else {
                Err(None)
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a [`NonNull`] pointer to the start of the buffer.",
        #[inline]
        pub const fn as_nonnull(&self) -> NonNull<T> {
            self.buf
        }
    }

    const_if! {
        "extra_const",
        "Gets a reference to the buffer as a [`Buf`].",
        #[inline]
        pub const fn as_buf(&self) -> Buf<'_, T> {
            Buf {
                buf: self.as_uninit_slice(),
                init: self.init,
            }
        }
    }

    const_if! {
        "extra_extra_const",
        "Gets a reference to the buffer as a [`Buf`], and its allocator.\n\nThe data will be \
        considered unowned after this operation.",
        pub const fn into_buf_with_alloc(self) -> (Buf<'static, T>, A) {
            let out = (
                Buf {
                    buf: unsafe {
                        &*(nonnull_slice_from_raw_parts(self.buf, self.init).as_ptr()
                            as *const [MaybeUninit<T>])
                    },
                    init: self.init,
                },
                unsafe { ptr::read(&self.alloc) },
            );
            forget(self);
            out
        }
    }

    /// Gets a reference to the buffer as a [`Buf`].
    ///
    /// The data will be considered unowned after this operation.
    pub fn into_buf(self) -> Buf<'static, T> {
        let (buf, init, size, _) = self.into_raw_parts();
        Buf {
            buf: unsafe { slice::from_raw_parts(buf.as_ptr() as *const MaybeUninit<T>, size) },
            init,
        }
    }

    /// Placeholder docs
    #[allow(clippy::missing_errors_doc)]
    // TODO: make sure this works
    pub fn into_chunks<const N: usize>(
        mut self,
    ) -> Result<OwnedBuf<[T; N], A>, VariableError<(), AllocError>> {
        if N == 0 {
            return Err(Soft(()));
        }


        if let Err(e) = self.truncate(self.init - self.init % N) {
            return Err(Hard(e));
        }

        let usable_size = self.size % N;
        if !T::IS_ZST && usable_size != 0 {
            // SAFETY: after the truncation, self.init will be less than usable_size.
            unsafe {
                if let Err(e) = self.set_size_unchecked(usable_size) {
                    return Err(Hard(e));
                }
            }
        }

        let (buf, _, _, a) = self.into_raw_parts();

        Ok(unsafe { OwnedBuf::from_raw_parts(buf.cast(), self.init / N, self.size / N, a) })
    }
}

// TODO: make sure all non-const traits which can be const (but aren't because they're in a trait)
//  have const, inherent versions.

impl<T, A: Alloc + Debug> Debug for OwnedBuf<T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("OwnedBuf")
            .field("buf", &self.buf)
            .field("init", &self.init)
            .field("size", &self.size)
            .field("alloc", &self.alloc)
            .finish()
    }
}

impl<T, A: Alloc + Default> Default for OwnedBuf<T, A> {
    #[inline]
    fn default() -> OwnedBuf<T, A> {
        OwnedBuf::new_unallocated_in(A::default())
    }
}

impl<T, A: Alloc> Deref for OwnedBuf<T, A> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, A: Alloc> DerefMut for OwnedBuf<T, A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_slice_mut()
    }
}

impl<T, A: Alloc> AsRef<[T]> for OwnedBuf<T, A> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, A: Alloc> AsMut<[T]> for OwnedBuf<T, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self.as_slice_mut()
    }
}

impl<T, A: Alloc> AsRef<[MaybeUninit<T>]> for OwnedBuf<T, A> {
    #[inline]
    fn as_ref(&self) -> &[MaybeUninit<T>] {
        self.as_uninit_slice()
    }
}

impl<T, A: Alloc> AsMut<[MaybeUninit<T>]> for OwnedBuf<T, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut [MaybeUninit<T>] {
        self.as_uninit_slice_mut()
    }
}

impl<'s, T, A: Alloc> From<&'s OwnedBuf<T, A>> for Buf<'s, T> {
    #[inline]
    fn from(owned: &'s OwnedBuf<T, A>) -> Buf<'s, T> {
        owned.as_buf()
    }
}

impl<'s, T, A: Alloc> From<&'s mut OwnedBuf<T, A>> for Buf<'s, T> {
    #[inline]
    fn from(owned: &'s mut OwnedBuf<T, A>) -> Buf<'s, T> {
        owned.as_buf()
    }
}

impl<T, A: Alloc> From<OwnedBuf<T, A>> for Buf<'static, T> {
    #[inline]
    fn from(owned: OwnedBuf<T, A>) -> Buf<'static, T> {
        owned.into_buf()
    }
}

impl<T, A: Alloc> Borrow<[T]> for OwnedBuf<T, A> {
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, A: Alloc> Borrow<[MaybeUninit<T>]> for OwnedBuf<T, A> {
    fn borrow(&self) -> &[MaybeUninit<T>] {
        self.as_uninit_slice()
    }
}

impl<T, A: Alloc> BorrowMut<[T]> for OwnedBuf<T, A> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_slice_mut()
    }
}

impl<T, A: Alloc> BorrowMut<[MaybeUninit<T>]> for OwnedBuf<T, A> {
    fn borrow_mut(&mut self) -> &mut [MaybeUninit<T>] {
        self.as_uninit_slice_mut()
    }
}

macro_rules! spec_from_impl {
    ($($extra_token:tt)?) => {
        impl<T: Clone, A: Alloc + Default> From<&[T]>
			for OwnedBuf<T, A>
		{
            #[track_caller]
            #[inline]
            $($extra_token)? fn from(slice: &[T]) -> OwnedBuf<T, A> {
                Buf::from(slice)
                    .clone_into_owned_in(A::default())
                    .expect("`<From<&[T]>>::from` failed")
            }
        }

        impl<T: Clone, A: Alloc + Default> From<&mut [T]>
			for OwnedBuf<T, A>
		{
            #[track_caller]
            #[inline]
            $($extra_token)? fn from(slice: &mut [T]) -> OwnedBuf<T, A> {
                OwnedBuf::from(&*slice)
            }
        }

        impl<T: Clone, A: Alloc + Default, const N: usize> From<&[T; N]>
			for OwnedBuf<T, A>
		{
            #[track_caller]
            #[inline]
            $($extra_token)? fn from(b_arr: &[T; N]) -> OwnedBuf<T, A> {
                <OwnedBuf<T, A> as From<&[T]>>::from(b_arr)
            }
        }

        impl<T: Clone, A: Alloc + Default, const N: usize> From<&mut [T; N]>
			for OwnedBuf<T, A>
		{
            #[track_caller]
            #[inline]
            $($extra_token)? fn from(b_arr: &mut [T; N]) -> OwnedBuf<T, A> {
                <OwnedBuf<T, A> as From<&[T]>>::from(b_arr)
            }
        }
    };
}

#[cfg(not(feature = "specialization"))]
spec_from_impl!();

#[cfg(feature = "specialization")]
spec_from_impl!(default);

#[cfg(feature = "specialization")]
impl<T: Copy, A: Alloc + Default> From<&[T]> for OwnedBuf<T, A> {
    #[track_caller]
    #[inline]
    fn from(slice: &[T]) -> OwnedBuf<T, A> {
        Buf::from(slice)
            .copy_into_owned_in(A::default())
            .expect("`<From<&[T]>>::from` failed")
    }
}

#[cfg(feature = "specialization")]
impl<T: Copy, A: Alloc + Default> From<&mut [T]> for OwnedBuf<T, A> {
    #[track_caller]
    #[inline]
    fn from(slice: &mut [T]) -> OwnedBuf<T, A> {
        OwnedBuf::from(&*slice)
    }
}

#[cfg(feature = "specialization")]
impl<T: Copy, A: Alloc + Default, const N: usize> From<&[T; N]> for OwnedBuf<T, A> {
    #[track_caller]
    #[inline]
    fn from(b_arr: &[T; N]) -> OwnedBuf<T, A> {
        Buf::from(b_arr)
            .copy_into_owned_in(A::default())
            .expect("`<From<&[T; N]>>::from` failed")
    }
}

#[cfg(feature = "specialization")]
impl<T: Copy, A: Alloc + Default, const N: usize> From<&mut [T; N]> for OwnedBuf<T, A> {
    #[track_caller]
    #[inline]
    fn from(b_arr: &mut [T; N]) -> OwnedBuf<T, A> {
        OwnedBuf::from(&*b_arr)
    }
}

#[cfg(feature = "nightly")]
//noinspection RsUnnecessaryQualifications
impl<T, A: Alloc + alloc::alloc::Allocator> From<OwnedBuf<T, A>> for alloc::vec::Vec<T, A> {
    fn from(owned: OwnedBuf<T, A>) -> alloc::vec::Vec<T, A> {
        let (buf, init, size, a) = owned.into_raw_parts();
        unsafe { alloc::vec::Vec::from_raw_parts_in(buf.as_ptr(), init, size, a) }
    }
}
#[cfg(not(feature = "nightly"))]
//noinspection RsUnnecessaryQualifications
impl<T> From<OwnedBuf<T>> for alloc::vec::Vec<T> {
    fn from(owned: OwnedBuf<T>) -> alloc::vec::Vec<T> {
        let (buf, init, size, _) = owned.into_raw_parts();
        unsafe { alloc::vec::Vec::from_raw_parts(buf.as_ptr(), init, size) }
    }
}

#[cfg(feature = "nightly")]
//noinspection RsUnnecessaryQualifications
impl<T, A: Alloc + alloc::alloc::Allocator> From<alloc::vec::Vec<T, A>> for OwnedBuf<T, A> {
    fn from(vec: alloc::vec::Vec<T, A>) -> OwnedBuf<T, A> {
        let (buf, init, size, a) = vec.into_parts_with_alloc();
        unsafe { OwnedBuf::from_raw_parts(buf, init, size, a) }
    }
}

// how has it taken 6 years to stabilize vec's into_parts method???
//
// #[cfg(not(feature = "nightly"))]
// impl<T> From<alloc::vec::Vec<T>> for OwnedBuf<T> {
//     fn from(vec: alloc::vec::Vec<T>) -> OwnedBuf<T> {
//         let (buf, init, size) = vec.into_parts();
//         unsafe {
//             OwnedBuf::from_raw_parts(buf, init, size, DefaultAlloc)
//         }
//     }
// }

impl<T: Clone, A: Alloc + Clone> Clone for OwnedBuf<T, A> {
    fn clone(&self) -> OwnedBuf<T, A> {
        Buf::from(self)
            .dupe_into_owned_in(self.alloc.clone())
            .expect("`OwnedBuf::clone` failed")
    }

    fn clone_from(&mut self, source: &OwnedBuf<T, A>) {
        source
            .as_slice()
            .clone_into_ob(self)
            .expect("`OwnedBuf::clone_from` failed");
    }
}

trait SpecCi<T, A: Alloc> {
    fn clone_into_ob(&self, target: &mut OwnedBuf<T, A>) -> Result<(), AllocError>;
}

macro_rules! spec_ci_impl {
    ($($extra_token:tt)?) => {
        impl<T: Clone, A: Alloc> SpecCi<T, A> for [T] {
            #[inline]
            $($extra_token)? fn clone_into_ob(
                &self,
                target: &mut OwnedBuf<T, A>
            ) -> Result<(), AllocError> {
                let _ = target.truncate(self.len());

                 let (init, tail) = self.split_at(target.len());

                target.clone_from_slice(init);
                // TEMPORARY: this solution works until extend_from_slice is implemented.
                match target.try_init_next_slice_grow(tail) {
                    Ok(()) => Ok(()),
                    Err(v_err) => match v_err {
                        Soft(_) => unsafe { core::hint::unreachable_unchecked() },
                        Hard((_, e)) => Err(e)
                    }
                }
            }
        }
    }
}

#[cfg(not(feature = "specialization"))]
spec_ci_impl!();

#[cfg(feature = "specialization")]
spec_ci_impl!(default);

#[cfg(feature = "specialization")]
impl<T: Copy, A: Alloc> SpecCi<T, A> for [T] {
    #[inline]
    fn clone_into_ob(&self, target: &mut OwnedBuf<T, A>) -> Result<(), AllocError> {
        target.clear();
        match target.try_init_next_slice_grow(self) {
            Ok(()) => Ok(()),
            Err(v_err) => match v_err {
                Soft(_) => unsafe { core::hint::unreachable_unchecked() },
                Hard((_, e)) => Err(e),
            },
        }
    }
}

trait SpecInitNextSlice<T, A: Alloc> {
    fn init_next_slice(buf: &mut OwnedBuf<T, A>, slice: &Self);
}

macro_rules! spec_init_next_slice_impl {
    ($($extra_token:tt)?) => {
        impl<T: Clone, A: Alloc> SpecInitNextSlice<T, A> for [T] {
            $($extra_token)? fn init_next_slice(buf: &mut OwnedBuf<T, A>, slice: &[T]) {
                let ptr = buf.as_nonnull().as_ptr();
                let mut guard = SliceAllocGuard::new(buf.as_nonnull(), buf.alloc(), buf.size);
                unsafe {
                    guard.set_init(buf.init);
                }

                for (i, elem) in slice.iter().enumerate() {
                    unsafe {
                        ptr.add(i).write(elem.clone());
                    }
                }

                forget(guard);
            }
        }
    };
}

#[cfg(not(feature = "specialization"))]
spec_init_next_slice_impl!();

#[cfg(feature = "specialization")]
spec_init_next_slice_impl!(default);

#[cfg(feature = "specialization")]
impl<T: Copy, A: Alloc> SpecInitNextSlice<T, A> for [T] {
    fn init_next_slice(buf: &mut OwnedBuf<T, A>, slice: &Self) {
        let ptr = unsafe { buf.as_nonnull().as_ptr().add(buf.init) };
        let mut guard = SliceAllocGuard::new(buf.as_nonnull(), buf.alloc(), buf.size);
        unsafe {
            guard.set_init(buf.init);
        }

        unsafe {
            ptr::copy_nonoverlapping(slice.as_ptr(), ptr, slice.len());
        }

        forget(guard);
    }
}

impl<T, A: Alloc, I: SliceIndex<[T]>> Index<I> for OwnedBuf<T, A> {
    type Output = I::Output;

    fn index(&self, index: I) -> &<OwnedBuf<T> as Index<I>>::Output {
        self.as_slice().index(index)
    }
}
impl<T, A: Alloc, I: SliceIndex<[T]>> IndexMut<I> for OwnedBuf<T, A> {
    fn index_mut(&mut self, index: I) -> &mut <OwnedBuf<T> as Index<I>>::Output {
        self.as_slice_mut().index_mut(index)
    }
}

impl<T: PartialEq, A: Alloc> PartialEq for OwnedBuf<T, A> {
    fn eq(&self, other: &OwnedBuf<T, A>) -> bool {
        self.eq(other.as_slice())
    }
}
impl<T: Eq, A: Alloc> Eq for OwnedBuf<T, A> {}

impl<T: PartialEq, A: Alloc> PartialEq<[T]> for OwnedBuf<T, A> {
    fn eq(&self, other: &[T]) -> bool {
        self.as_slice().eq(other)
    }
}
impl<'s, T: PartialEq, A: Alloc> PartialEq<Buf<'s, T>> for OwnedBuf<T, A> {
    fn eq(&self, other: &Buf<'s, T>) -> bool {
        self.as_buf().eq(other)
    }
}

impl<T: PartialOrd, A: Alloc> PartialOrd for OwnedBuf<T, A> {
    fn partial_cmp(&self, other: &OwnedBuf<T, A>) -> Option<Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}
impl<T: PartialOrd, A: Alloc> PartialOrd<[T]> for OwnedBuf<T, A> {
    fn partial_cmp(&self, other: &[T]) -> Option<Ordering> {
        self.as_slice().partial_cmp(other)
    }
}

impl<T: Ord, A: Alloc> Ord for OwnedBuf<T, A> {
    fn cmp(&self, other: &OwnedBuf<T, A>) -> Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<T: Hash, A: Alloc> Hash for OwnedBuf<T, A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<'s, T, A: Alloc> IntoIterator for &'s OwnedBuf<T, A> {
    type Item = &'s T;
    type IntoIter = slice::Iter<'s, T>;

    fn into_iter(self) -> slice::Iter<'s, T> {
        self.as_slice().iter()
    }
}
impl<'s, T, A: Alloc> IntoIterator for &'s mut OwnedBuf<T, A> {
    type Item = &'s mut T;
    type IntoIter = slice::IterMut<'s, T>;

    fn into_iter(self) -> slice::IterMut<'s, T> {
        self.as_slice_mut().iter_mut()
    }
}

// impl<T, A: Alloc> IntoIterator for OwnedBuf<T, A> {
//     type Item = T;
//     type IntoIter = OwnedIter<T, A>;
//
//     fn into_iter(self) -> OwnedIter<T, A> {
//         let OwnedBuf {
//             buf,
//             init,
//             size,
//             alloc,
//             ..
//         } = self;
//         OwnedIter {
//             buf,
//             init,
//             size,
//             idx: 0,
//             bidx: init,
//             alloc: ManuallyDrop::new(alloc),
//             _marker: PhantomData,
//         }
//     }
// }

#[cfg(all(feature = "drop_for_owned", not(feature = "zero_drop_for_owned")))]
impl<T, A: Alloc> Drop for OwnedBuf<T, A> {
    fn drop(&mut self) {
        self.reset();
    }
}

#[cfg(feature = "zero_drop_for_owned")]
impl<T, A: Alloc> Drop for OwnedBuf<T, A> {
    fn drop(&mut self) {
        self.reset_zero();
    }
}

/// A buffer of multiple `MaybeUninit<T>`, with an initialization counter.
///
/// This is the 'unowned' form of [`OwnedBuf`].
#[derive(Debug, Copy, Clone)]
pub struct Buf<'s, T> {
    /// The buffer.
    pub buf: &'s [MaybeUninit<T>],
    /// The count of initialized elements in the buffer.
    pub init: usize,
}

impl<'s, T> Default for Buf<'s, T> {
    fn default() -> Buf<'s, T> {
        Buf { buf: &[], init: 0 }
    }
}

impl<T: Hash> Hash for Buf<'_, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.init_buf().hash(state);
    }
}

impl<'s, T> From<&'s [T]> for Buf<'s, T> {
    #[inline]
    fn from(elems: &'s [T]) -> Buf<'s, T> {
        Buf {
            buf: unsafe { &*(elems as *const [T] as *const [MaybeUninit<T>]) },
            init: elems.len(),
        }
    }
}

impl<'s, T> From<Buf<'s, T>> for &'s [T] {
    #[inline]
    fn from(val: Buf<'s, T>) -> &'s [T] {
        val.init_buf()
    }
}

impl<'s, T> From<Buf<'s, T>> for &'s [MaybeUninit<T>] {
    #[inline]
    fn from(val: Buf<'s, T>) -> &'s [MaybeUninit<T>] {
        val.buf
    }
}

impl<'s, T> From<&'s mut [T]> for Buf<'s, T> {
    #[inline]
    fn from(elems: &'s mut [T]) -> Buf<'s, T> {
        Buf::from(&*elems)
    }
}

impl<'s, T, const N: usize> From<&'s [T; N]> for Buf<'s, T> {
    #[inline]
    fn from(elems: &'s [T; N]) -> Buf<'s, T> {
        <Buf<'s, T> as From<&[T]>>::from(elems)
    }
}

impl<'s, T, const N: usize> From<&'s mut [T; N]> for Buf<'s, T> {
    #[inline]
    fn from(elems: &'s mut [T; N]) -> Buf<'s, T> {
        <Buf<'s, T> as From<&[T]>>::from(elems)
    }
}

impl<'s, T> IntoIterator for Buf<'s, T> {
    type Item = &'s T;
    type IntoIter = slice::Iter<'s, T>;

    #[inline]
    fn into_iter(self) -> slice::Iter<'s, T> {
        self.init_buf().iter()
    }
}

impl<'s, T> IntoIterator for &'s Buf<'s, T> {
    type Item = &'s T;
    type IntoIter = slice::Iter<'s, T>;

    #[inline]
    fn into_iter(self) -> slice::Iter<'s, T> {
        self.init_buf().iter()
    }
}

impl<T> Deref for Buf<'_, T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.init_buf()
    }
}

impl<T: PartialEq> PartialEq for Buf<'_, T> {
    #[inline]
    fn eq(&self, other: &Buf<'_, T>) -> bool {
        self.init == other.init && self.init_buf().eq(other.init_buf())
    }
}
impl<T: Eq> Eq for Buf<'_, T> {}

impl<T: PartialEq> PartialEq<[T]> for Buf<'_, T> {
    #[inline]
    fn eq(&self, other: &[T]) -> bool {
        self.init == other.len() && self.init_buf().eq(other)
    }
}

impl<T: PartialOrd> PartialOrd for Buf<'_, T> {
    #[inline]
    fn partial_cmp(&self, other: &Buf<'_, T>) -> Option<Ordering> {
        // delegate to partialord<[T]>
        self.partial_cmp(other.init_buf())
    }
}
impl<T: Ord> Ord for Buf<'_, T> {
    #[inline]
    fn cmp(&self, other: &Buf<'_, T>) -> Ordering {
        self.init
            .cmp(&other.init)
            .then_with(|| self.init_buf().cmp(other.init_buf()))
    }
}

impl<T: PartialOrd> PartialOrd<[T]> for Buf<'_, T> {
    #[inline]
    fn partial_cmp(&self, other: &[T]) -> Option<Ordering> {
        self.init.partial_cmp(&other.len()).and_then(|cmp| {
            if cmp == Ordering::Equal {
                self.init_buf().partial_cmp(other)
            } else {
                Some(cmp)
            }
        })
    }
}

impl<T> Buf<'_, T> {
    /// Creates a new owned buffer with a size equivalent to the contained slice, and clones all
    /// initialized elements into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn clone_into_owned(&self) -> Result<OwnedBuf<T>, AllocError>
    where
        T: Clone,
    {
        self.clone_into_owned_in(DefaultAlloc)
    }

    /// Creates a new owned buffer with a size equivalent to the contained slice and copies all
    /// initialized elements into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[inline]
    pub fn copy_into_owned(&self) -> Result<OwnedBuf<T>, AllocError>
    where
        T: Copy,
    {
        self.copy_into_owned_in(DefaultAlloc)
    }

    /// Creates a new owned buffer with a size equivalent to the contained slice, and copies all
    /// initialized elements into it. This method has no `T: Copy` bound.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    ///
    /// # Safety
    ///
    /// The caller must ensure the performed copying of elements is safe.
    #[inline]
    pub unsafe fn copy_into_owned_unchecked(&self) -> Result<OwnedBuf<T>, AllocError> {
        self.copy_into_owned_in_unchecked(DefaultAlloc)
    }

    /// Creates a new owned buffer with a size equivalent to the contained slice and a given
    /// allocator, then duplicates all initialized elements into it using either `Copy` or `Clone`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    pub fn dupe_into_owned(&self) -> Result<OwnedBuf<T>, AllocError> {
        self.dupe_into_owned_in(DefaultAlloc)
    }

    /// Creates a new owned buffer with a size equivalent to the contained slice and a given
    /// allocator, then clones all initialized elements into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn clone_into_owned_in<A: Alloc>(&self, alloc: A) -> Result<OwnedBuf<T, A>, AllocError>
    where
        T: Clone,
    {
        let (buf, _, size, alloc) = OwnedBuf::new_in(self.buf.len(), alloc)?.into_raw_parts();
        let mut buf = SliceAllocGuard::new(buf, &alloc, size);
        for i in 0..self.init {
            unsafe {
                match buf.init((&*self.buf.get_unchecked(i).as_ptr()).clone()) {
                    Ok(()) => {}
                    Err(_) => core::hint::unreachable_unchecked(),
                }
            }
        }
        Ok(OwnedBuf {
            buf: buf.release().cast::<T>(),
            init: self.init,
            size,
            alloc,
            _marker: PhantomData,
        })
    }

    /// Creates a new owned buffer with a size equivalent to the contained slice and a given
    /// allocator, then copies all initialized elements into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[inline]
    pub fn copy_into_owned_in<A: Alloc>(&self, alloc: A) -> Result<OwnedBuf<T, A>, AllocError>
    where
        T: Copy,
    {
        unsafe { self.copy_into_owned_in_unchecked(alloc) }
    }

    /// Creates a new owned buffer with a size equivalent to the contained slice and a given
    /// allocator, then copies all initialized elements into it. This method has no `T: Copy` bound.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    ///
    /// # Safety
    ///
    /// The caller must ensure the performed copying of elements is safe.
    #[inline]
    pub unsafe fn copy_into_owned_in_unchecked<A: Alloc>(
        &self,
        alloc: A,
    ) -> Result<OwnedBuf<T, A>, AllocError> {
        let (buf, _, size, alloc) = OwnedBuf::new_in(self.buf.len(), alloc)?.into_raw_parts();
        // why was this a loop before??
        ptr::copy_nonoverlapping(self.buf.as_ptr() as *const T, buf.as_ptr(), self.init);
        Ok(OwnedBuf {
            buf,
            init: self.init,
            size,
            alloc,
            _marker: PhantomData,
        })
    }

    /// Creates a new owned buffer with a size equivalent to the contained slice and a given
    /// allocator, then duplicates all initialized elements into it using either `Copy` or `Clone`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[inline]
    pub fn dupe_into_owned_in<A: Alloc>(&self, alloc: A) -> Result<OwnedBuf<T, A>, AllocError>
    where
        T: Clone,
    {
        trait SpecDupeSlice<T> {
            fn dupe(&self, dst: *mut T);
        }

        macro_rules! spec_dupe_slice_impl {
            ($($extra_token:tt)?) => {
                impl<T: Clone> SpecDupeSlice<T> for [T] {
                    $($extra_token)? fn dupe(&self, dst: *mut T) {
                                // TODO: completely switch to CloneIntoUninit (here and with
                                //  OwnedBuf's other spec stuff) when stable so we don't have to
                                //  use this terrible loop
                        for (i, elem) in self.iter().enumerate() {
                            unsafe {
                                dst.add(i).write(elem.clone());
                            }
                        }
                    }
                }
            };
        }

        #[cfg(not(feature = "specialization"))]
        spec_dupe_slice_impl!();

        #[cfg(feature = "specialization")]
        spec_dupe_slice_impl!(default);

        #[cfg(feature = "specialization")]
        impl<T: Copy> SpecDupeSlice<T> for [T] {
            fn dupe(&self, dst: *mut T) {
                unsafe {
                    ptr::copy_nonoverlapping(self.as_ptr(), dst, self.len());
                }
            }
        }

        let (buf_ptr, _, size, alloc) = OwnedBuf::new_in(self.buf.len(), alloc)?.into_raw_parts();

        unsafe {
            <[T] as SpecDupeSlice<T>>::dupe(
                &*(slice_ptr_from_raw_parts(self.buf.as_ptr().cast::<T>() as *mut T, self.init)
                    as *const [T]),
                buf_ptr.as_ptr(),
            );
        }

        Ok(OwnedBuf {
            buf: buf_ptr,
            init: self.init,
            size,
            alloc,
            _marker: PhantomData,
        })
    }

    /// Gets a pointer to the entire buffer.
    #[allow(clippy::must_use_candidate)]
    #[inline]
    pub const fn buf_ptr(&self) -> NonNull<[MaybeUninit<T>]> {
        unsafe {
            NonNull::new_unchecked(self.buf as *const [MaybeUninit<T>] as *mut [MaybeUninit<T>])
        }
    }

    /// Gets a pointer to the initialized portion of the buffer.
    #[must_use]
    #[inline]
    pub const fn init_buf_ptr(&self) -> NonNull<[T]> {
        nonnull_slice_from_raw_parts(
            unsafe { NonNull::new_unchecked(self.buf.as_ptr() as *mut T) },
            self.init,
        )
    }

    const_if! {
        "extra_const",
        "Gets a pointer to the uninitialized portion of the buffer.",
        #[must_use]
        #[inline]
        pub const fn uninit_buf_ptr(&self) -> NonNull<[MaybeUninit<T>]> {
            nonnull_slice_from_raw_parts(
                unsafe {
                    NonNull::new_unchecked(self.buf.as_ptr().add(self.init) as *mut MaybeUninit<T>)
                },
                self.buf.len() - self.init,
            )
        }
    }
}

impl<'s, T> Buf<'s, T> {
    /// Gets a slice of the entire buffer.
    #[must_use]
    #[inline]
    pub const fn buf(&self) -> &'s [MaybeUninit<T>] {
        self.buf
    }

    const_if! {
        "extra_const",
        "Gets a slice of the initialized portion of the buffer.",
        #[must_use]
        #[inline]
        pub const fn init_buf(&self) -> &'s [T] {
            unsafe {
                &*(nonnull_slice_from_raw_parts(self.buf_ptr().cast(), self.init).as_ptr()
                    as *const [T])
            }
        }
    }

    const_if! {
        "extra_const",
        "Gets a slice of the uninitialized portion of the buffer.",
        #[must_use]
        #[inline]
        pub const fn uninit_buf(&self) -> &'s [MaybeUninit<T>] {
            unsafe {
                &*(nonnull_slice_from_raw_parts(
                    self.uninit_buf_ptr().cast(),
                    self.buf.len() - self.init,
                )
                    .as_ptr() as *const [MaybeUninit<T>]
                )
            }
        }
    }
}

impl<T> Buf<'static, T> {
    const_if! {
        "extra_const",
        "Converts back into an [`OwnedBuf`] with the given allocator.\n\nThis method assumes the \
        elements are unowned. If this method has already been called on a copy of this buffer, \
        this may result in undefined behavior.\n\n# Safety\n\nThe contained elements must be \
        unowned and allocated using `alloc`.",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const unsafe fn into_owned<A: Alloc>(self, alloc: A) -> OwnedBuf<T, A> {
            let Buf { init, buf: elems } = self;
            OwnedBuf {
                buf: NonNull::new_unchecked(self.buf as *const [MaybeUninit<T>] as *mut T),
                init,
                size: elems.len(),
                alloc,
                _marker: PhantomData,
            }
        }
    }
}
