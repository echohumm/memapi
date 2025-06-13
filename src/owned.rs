use crate::helpers::SliceAllocGuard;
use crate::{
    Alloc, AllocError, DefaultAlloc, SizedProps,
    owned::VariableError::{Hard, Soft},
};
use core::borrow::{Borrow, BorrowMut};
use core::{
    alloc::Layout,
    error::Error,
    fmt::{self, Debug, Display, Formatter},
    mem::{ManuallyDrop, MaybeUninit, forget, transmute},
    ops::{Deref, DerefMut},
    ptr::{self, NonNull, replace},
    slice,
};

/// An error which can be soft or hard.
pub enum VariableError<S, H> {
    /// A soft error
    Soft(S),
    /// A hard error.
    Hard(H),
}

impl<S: Debug, H: Debug> Debug for VariableError<S, H> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Soft(s) => write!(f, "Soft error: {s:?}"),
            Hard(h) => write!(f, "Hard error: {h:?}"),
        }
    }
}

impl<S: Display, H: Display> Display for VariableError<S, H> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Soft(s) => write!(f, "Soft error: {s}"),
            Hard(h) => write!(f, "Hard error: {h}"),
        }
    }
}

impl<S: Display + Debug, H: Display + Debug> Error for VariableError<S, H> {}

//noinspection RsUnnecessaryQualifications
/// An owned buffer of multiple `T` allocated using `A`.
///
/// This is pretty much a low-level, minimal [`Vec`](alloc::vec::Vec), aside from requiring a
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
}

impl<T, A: Alloc> Debug for OwnedBuf<T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("OwnedBuf")
            .field("buf", &self.buf)
            .field("init", &self.init)
            .field("size", &self.size)
            .finish_non_exhaustive()
    }
}

impl<T> OwnedBuf<T> {
    /// Creates a new owned buffer of `T` with the given length, in the default allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    pub fn new(len: usize) -> Result<OwnedBuf<T>, AllocError> {
        OwnedBuf::new_in(len, DefaultAlloc)
    }

    /// Creates a new, unallocated owned buffer of `T`, set to use the default allocator for future
    /// allocations.
    #[must_use]
    #[inline]
    pub const fn new_unallocated() -> OwnedBuf<T> {
        OwnedBuf::new_unallocated_in(DefaultAlloc)
    }
}

impl<T, A: Alloc> OwnedBuf<T, A> {
    /// Creates a new owned buffer of `T` with the given length, in the given allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    pub fn new_in(len: usize, alloc: A) -> Result<OwnedBuf<T, A>, AllocError> {
        Ok(OwnedBuf {
            buf: alloc.alloc_slice::<T>(len)?.cast(),
            init: 0,
            size: len,
            alloc,
        })
    }

    /// Creates a new, unallocated owned buffer of `T`, set to use the given allocator for future
    /// allocations.
    #[must_use]
    #[inline]
    pub const fn new_unallocated_in(alloc: A) -> OwnedBuf<T, A> {
        OwnedBuf {
            buf: NonNull::dangling(),
            init: 0,
            size: 0,
            alloc,
        }
    }

    /// Breaks the owned buffer into its raw data.
    pub fn into_raw_parts(self) -> (NonNull<T>, usize, usize, A) {
        let me = ManuallyDrop::new(self);
        (me.buf, me.init, me.size, unsafe {
            ptr::read(&raw const me.alloc)
        })
    }

    /// Creates a new owned buffer of `T` from the given parts.
    ///
    /// # Safety
    ///
    /// The caller must ensure `buf` points to a valid buffer of `init` count initialized `T` and a
    /// capacity of `size`, allocated using `alloc`.
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
            size,
            alloc,
        }
    }

    /// Returns the total number of elements in the buffer.
    #[inline]
    pub const fn size(&self) -> usize {
        self.size
    }

    /// Returns the number of initialized elements in the buffer.
    #[inline]
    pub const fn initialized(&self) -> usize {
        self.init
    }

    /// Sets the initialized element count.
    ///
    /// # Safety
    ///
    /// All elements up to `init` elements must be guaranteed to be initialized before use.
    #[inline]
    pub const unsafe fn set_initialized(&mut self, init: usize) {
        self.init = init;
    }

    /// Gets a reference to the contained allocator.
    #[inline]
    pub const fn alloc(&self) -> &A {
        &self.alloc
    }

    /// Gets a mutable reference to the contained allocator.
    #[inline]
    pub const fn alloc_mut(&mut self) -> &mut A {
        &mut self.alloc
    }

    /// Gets a pointer to the entire buffer.
    #[inline]
    pub const fn buf_ptr(&self) -> NonNull<[MaybeUninit<T>]> {
        NonNull::slice_from_raw_parts(self.buf.cast::<MaybeUninit<T>>(), self.size)
    }

    /// Gets a pointer to the initialized portion of the buffer.
    #[inline]
    pub const fn init_buf_ptr(&self) -> NonNull<[T]> {
        NonNull::slice_from_raw_parts(self.buf.cast::<T>(), self.init)
    }

    /// Gets a pointer to the uninitialized portion of the buffer.
    #[inline]
    pub const fn uninit_buf_ptr(&self) -> NonNull<[MaybeUninit<T>]> {
        NonNull::slice_from_raw_parts(
            unsafe { self.buf.add(self.init).cast::<MaybeUninit<T>>() },
            self.size - self.init,
        )
    }

    /// Gets a slice of the entire buffer.
    #[inline]
    pub const fn buf(&self) -> &[MaybeUninit<T>] {
        unsafe { &*self.buf_ptr().as_ptr() }
    }

    /// Gets a slice of the initialized portion of the buffer.
    #[inline]
    pub const fn init_buf(&self) -> &[T] {
        unsafe { &*self.init_buf_ptr().as_ptr() }
    }

    /// Gets a slice of the uninitialized portion of the buffer.
    #[inline]
    pub const fn uninit_buf(&self) -> &[MaybeUninit<T>] {
        unsafe { &*self.uninit_buf_ptr().as_ptr() }
    }

    /// Gets a mutable slice of the entire buffer.
    #[inline]
    pub const fn buf_mut(&mut self) -> &mut [MaybeUninit<T>] {
        unsafe { &mut *self.buf_ptr().as_ptr() }
    }

    /// Gets a mutable slice of the initialized portion of the buffer.
    #[inline]
    pub const fn init_buf_mut(&mut self) -> &mut [T] {
        unsafe { &mut *self.init_buf_ptr().as_ptr() }
    }

    /// Gets a mutable slice of the uninitialized portion of the buffer.
    #[inline]
    pub const fn uninit_buf_mut(&mut self) -> &mut [MaybeUninit<T>] {
        unsafe { &mut *self.uninit_buf_ptr().as_ptr() }
    }

    /// Attempts to initialize the next element.
    ///
    /// # Errors
    ///
    /// Returns `Err(val)` if at capacity.
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

    /// Initializes the next element without checking for space.
    ///
    /// # Safety
    ///
    /// The caller must ensure `self.init < self.size`
    #[track_caller]
    #[inline]
    pub const unsafe fn init_next_unchecked(&mut self, val: T) {
        self.buf.as_ptr().add(self.init).write(val);
        self.init += 1;
    }

    /// Removes and returns the last element from the initialized portion of the buffer if it
    /// exists.
    #[inline]
    pub const fn remove_last(&mut self) -> Option<T> {
        if self.init != 0 {
            Some(unsafe { self.remove_last_unchecked() })
        } else {
            None
        }
    }

    /// Removes and returns the last element from the initialized portion of the buffer.
    ///
    /// # Safety
    ///
    /// The caller must ensure there is an initialized element to remove.
    #[track_caller]
    #[inline]
    pub const unsafe fn remove_last_unchecked(&mut self) -> T {
        self.init -= 1;
        self.buf.as_ptr().add(self.init).read()
    }

    /// Removes and returns the element at the given index from the initialized portion of the
    /// buffer if it exists.
    pub const fn remove(&mut self, idx: usize) -> Option<T> {
        if idx < self.init {
            Some(unsafe { self.remove_unchecked(idx) })
        } else {
            None
        }
    }

    /// Removes and returns the element at the given index.
    ///
    /// # Safety
    ///
    /// The caller must ensure the index is in the bounds of the initialized buffer.
    #[track_caller]
    #[inline]
    pub const unsafe fn remove_unchecked(&mut self, idx: usize) -> T {
        let src = self.get_ptr_unchecked(idx);
        let value = src.read();
        unsafe {
            src.add(1).copy_to(src, self.init - idx - 1);
        }
        self.init -= 1;
        value
    }

    /// Replaces the last element of the initialized portion of the buffer.
    ///
    /// # Errors
    ///
    /// Returns `Err(val)` if the buffer is empty. Otherwise, returns `Ok(replaced_val)`.
    #[inline]
    pub const fn replace_last(&mut self, val: T) -> Result<T, T> {
        self.replace(self.init - 1, val)
    }

    /// Replaces the element at the given index from the initialized portion of the buffer.
    ///
    /// # Errors
    ///
    /// Returns `Err(val)` if the index is out of bounds. Otherwise, returns `Ok(replaced_val)`.
    #[inline]
    pub const fn replace(&mut self, idx: usize, val: T) -> Result<T, T> {
        if idx <= self.init {
            Ok(unsafe { replace(self.get_ptr_unchecked(idx).as_ptr(), val) })
        } else {
            Err(val)
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
        match self.expand_to_fit(self.init + 1) {
            Ok(()) => {}
            Err(e) => return Err(Hard((val, e))),
        }

        unsafe {
            self.insert_unchecked(idx, val);
        }

        Ok(())
    }

    /// Attempts to insert `val` at the given `idx`.
    ///
    /// # Errors
    ///
    /// - `Err(val)` if the index is out of bounds or there is no space for the element.
    pub const fn try_insert(&mut self, idx: usize, val: T) -> Result<(), T> {
        if idx > self.init || self.init == self.size {
            return Err(val);
        }

        unsafe {
            self.insert_unchecked(idx, val);
        }

        Ok(())
    }

    /// Inserts `val` at the given `idx`.
    ///
    /// # Safety
    ///
    /// The caller must ensure `idx` is in bounds and their is space for a new element.
    pub const unsafe fn insert_unchecked(&mut self, idx: usize, val: T) {
        let dst = self.get_ptr_unchecked(idx);
        if idx != self.init {
            dst.copy_to_nonoverlapping(dst.add(1), self.init - idx);
        }
        dst.write(val);
        self.init += 1;
    }

    // TODO: add slice replacing and extending

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
    pub fn try_insert_slice_grow<A2: Alloc>(
        &mut self,
        idx: usize,
        slice: OwnedBuf<T, A2>,
    ) -> Result<(), VariableError<OwnedBuf<T, A2>, (OwnedBuf<T, A2>, AllocError)>> {
        if idx > self.init {
            return Err(Soft(slice));
        }
        match self.expand_to_fit(self.init + slice.len()) {
            Ok(()) => {}
            Err(e) => return Err(Hard((slice, e))),
        }

        unsafe {
            self.insert_slice_unchecked(idx, slice);
        }

        Ok(())
    }

    /// Attempts to insert `slice` at the given `idx`.
    ///
    /// # Errors
    ///
    /// - `Err(slice)` if the index is out of bounds or there is no space for some elements of the
    ///   slice.
    pub fn try_insert_slice<A2: Alloc>(
        &mut self,
        idx: usize,
        slice: OwnedBuf<T, A2>,
    ) -> Result<(), OwnedBuf<T, A2>> {
        if idx > self.init || self.init + slice.len() > self.size {
            return Err(slice);
        }

        unsafe {
            self.insert_slice_unchecked(idx, slice);
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
    pub unsafe fn insert_slice_unchecked<A2: Alloc>(&mut self, idx: usize, slice: OwnedBuf<T, A2>) {
        // destination of the slice
        let dst = self.get_ptr_unchecked(idx);
        // shift elements over to make space as necessary
        if idx != self.init {
            dst.copy_to_nonoverlapping(dst.add(slice.init), self.init - idx);
        }
        // pointer to initialized elements
        let src = slice.as_slice_ptr().as_ptr();
        // write in the elements
        src.cast::<T>()
            .copy_to_nonoverlapping(self.buf.as_ptr().add(idx), slice.init);
        // deallocate the original buffer
        slice
            .alloc
            .dealloc_n(NonNull::new_unchecked(src.cast::<T>()), slice.size);
        // noop but stops the non-consumed warning.
        forget(slice);
        // update initialized element count
        self.init += src.len();
    }

    /// Removes exactly `len` elements from this buffer, starting at `idx`, and returns them in a
    /// new [`OwnedBuf`] with the same allocator (cloned).
    ///
    /// # Returns
    ///
    /// - `Some(Ok(buf))` if `idx + len` is within bounds and allocation for the returned buffer
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
    /// - `Some(Ok(buf))` if `idx + len` is within bounds and allocation for the returned buffer
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
            self.buf
                .as_ptr()
                .add(idx + len)
                .copy_to(self.buf.as_ptr().add(idx), self.init - idx);
        }
        Ok(new_buf)
    }

    /// Gets a pointer to the element at the given `idx` if it is initialized.
    #[inline]
    pub const fn get_ptr(&self, idx: usize) -> Option<NonNull<T>> {
        if idx < self.init {
            Some(unsafe { self.get_ptr_unchecked(idx) })
        } else {
            None
        }
    }

    /// Gets a reference to the element at the given `idx` if it is initialized.
    #[inline]
    pub const fn get(&self, idx: usize) -> Option<&T> {
        if idx < self.init {
            Some(unsafe { self.get_unchecked(idx) })
        } else {
            None
        }
    }

    /// Gets a mutable reference to the element at the given `idx` if it is initialized.
    #[inline]
    pub const fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        if idx < self.init {
            Some(unsafe { self.get_mut_unchecked(idx) })
        } else {
            None
        }
    }

    /// Gets a pointer to the uninitialized element at the given `idx` if it exists.
    #[inline]
    pub const fn get_uninit_ptr(&self, idx: usize) -> Option<NonNull<MaybeUninit<T>>> {
        if idx < self.size {
            Some(unsafe { self.get_ptr_unchecked(idx).cast() })
        } else {
            None
        }
    }

    /// Gets a reference to the uninitialized element at the given `idx` if it exists.
    #[inline]
    pub const fn get_uninit(&self, idx: usize) -> Option<&MaybeUninit<T>> {
        if idx < self.size {
            Some(unsafe { &*self.get_ptr_unchecked(idx).cast().as_ptr() })
        } else {
            None
        }
    }

    /// Gets a mutable reference to the uninitialized element at the given `idx` if it exists.
    #[inline]
    pub const fn get_uninit_mut(&mut self, idx: usize) -> Option<&mut MaybeUninit<T>> {
        if idx < self.size {
            Some(unsafe { &mut *self.get_ptr_unchecked(idx).cast().as_ptr() })
        } else {
            None
        }
    }

    /// Gets a pointer to the element at the given `idx` if it is initialized, or a pointer to the
    /// uninitialized element if it exists.
    ///
    /// # Errors
    ///
    /// - `Err(None)` if the index is entirely out of bounds.
    /// - `Err(Some(uninit_ptr))` if the index is out of the initialized buffer, but still in the
    ///   buffer.
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

    /// Gets a reference to the element at the given `idx` if it is initialized, or a reference to
    /// the uninitialized element if it exists.
    ///
    /// # Errors
    ///
    /// - `Err(None)` if the index is entirely out of bounds.
    /// - `Err(Some(uninit_ptr))` if the index is out of the initialized buffer, but still in the
    ///   buffer.
    #[inline]
    pub const fn try_get(&self, idx: usize) -> Result<&T, Option<&MaybeUninit<T>>> {
        if idx < self.init {
            Ok(unsafe { self.get_unchecked(idx) })
        } else {
            Err(self.get_uninit(idx))
        }
    }

    /// Gets a mutable reference to the element at the given `idx` if it is initialized, or a
    /// mutable reference to the uninitialized element if it exists.
    ///
    /// # Errors
    ///
    /// - `Err(None)` if the index is entirely out of bounds.
    /// - `Err(Some(uninit_ptr))` if the index is out of the initialized buffer, but still in the
    ///   buffer.
    #[inline]
    pub const fn try_get_mut(&mut self, idx: usize) -> Result<&mut T, Option<&mut MaybeUninit<T>>> {
        if idx < self.init {
            Ok(unsafe { self.get_mut_unchecked(idx) })
        } else {
            Err(self.get_uninit_mut(idx))
        }
    }

    /// Gets a pointer to the element at the given `idx`.
    ///
    /// # Safety
    ///
    /// The caller must ensure the index is in bounds.
    #[track_caller]
    #[inline]
    pub const unsafe fn get_ptr_unchecked(&self, idx: usize) -> NonNull<T> {
        unsafe { self.buf.add(idx) }
    }

    /// Gets a reference to the element at the given `idx`.
    ///
    /// # Safety
    ///
    /// The caller must ensure the index is in bounds.
    #[track_caller]
    #[inline]
    pub const unsafe fn get_unchecked(&self, idx: usize) -> &T {
        unsafe { &*self.get_ptr_unchecked(idx).as_ptr() }
    }

    /// Gets a mutable reference to the element at the given `idx`.
    ///
    /// # Safety
    ///
    /// The caller must ensure the index is in bounds.
    #[track_caller]
    #[inline]
    pub const unsafe fn get_mut_unchecked(&mut self, idx: usize) -> &mut T {
        unsafe { &mut *self.get_ptr_unchecked(idx).as_ptr() }
    }

    /// Gets a pointer to a portion of the initialized buffer if the parameters are in bounds.
    #[inline]
    pub const fn get_slice_ptr(&self, start: usize, len: usize) -> Option<NonNull<[T]>> {
        if start + len < self.init {
            Some(unsafe { self.get_slice_ptr_unchecked(start, len) })
        } else {
            None
        }
    }

    /// Gets a reference to a portion of the initialized buffer if the parameters are in bounds.
    #[inline]
    pub const fn get_slice(&self, start: usize, len: usize) -> Option<&[T]> {
        if start + len < self.init {
            Some(unsafe { self.get_slice_unchecked(start, len) })
        } else {
            None
        }
    }

    /// Gets a mutable reference to a portion of the initialized buffer if the parameters are in
    /// bounds.
    #[inline]
    pub const fn get_slice_mut(&mut self, start: usize, len: usize) -> Option<&mut [T]> {
        if start + len < self.init {
            Some(unsafe { self.get_slice_mut_unchecked(start, len) })
        } else {
            None
        }
    }

    /// Gets a pointer to a portion of the buffer if the parameters are in bounds.
    #[inline]
    pub const fn get_uninit_slice_ptr(
        &self,
        start: usize,
        len: usize,
    ) -> Option<NonNull<[MaybeUninit<T>]>> {
        if start + len < self.size {
            // transmute works here because they have the same underlying type (*mut T, and the same
            //  metadata.)
            Some(unsafe {
                transmute::<NonNull<[T]>, NonNull<[MaybeUninit<T>]>>(
                    self.get_slice_ptr_unchecked(start, len),
                )
            })
        } else {
            None
        }
    }

    /// Gets a reference to a portion of the buffer if the parameters are in bounds.
    #[inline]
    pub const fn get_uninit_slice(&self, start: usize, len: usize) -> Option<&[MaybeUninit<T>]> {
        if start + len < self.size {
            Some(unsafe {
                &*(self.get_slice_ptr_unchecked(start, len).as_ptr() as *const [MaybeUninit<T>])
            })
        } else {
            None
        }
    }

    /// Gets a mutable reference to a portion of the buffer if the parameters are in bounds.
    #[inline]
    pub const fn get_uninit_slice_mut(
        &mut self,
        start: usize,
        len: usize,
    ) -> Option<&mut [MaybeUninit<T>]> {
        if start + len < self.size {
            Some(unsafe {
                &mut *(self.get_slice_ptr_unchecked(start, len).as_ptr() as *mut [MaybeUninit<T>])
            })
        } else {
            None
        }
    }

    /// Gets a pointer to a portion of the initialized buffer if in bounds, or a pointer to a
    /// portion of the buffer if not.
    ///
    /// # Errors
    ///
    /// - `Err(None)` if the index is entirely out of bounds.
    /// - `Err(Some(uninit_ptr))` if the index is out of the initialized buffer, but still in the
    ///   buffer.
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

    /// Gets a reference to a portion of the initialized buffer if in bounds, or a reference to a
    /// portion of the buffer if not.
    ///
    /// # Errors
    ///
    /// - `Err(None)` if the index is entirely out of bounds.
    /// - `Err(Some(uninit_ref))` if the index is out of the initialized buffer, but still in the
    ///   buffer.
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

    /// Gets a mutable reference to a portion of the initialized buffer if in bounds, or a mutable
    /// reference to a portion of the buffer if not.
    ///
    /// # Errors
    ///
    /// - `Err(None)` if the index is entirely out of bounds.
    /// - `Err(Some(uninit_mut))` if the index is out of the initialized buffer, but still in the
    ///   buffer.
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

    /// Gets a pointer to a portion of the buffer.
    ///
    /// # Safety
    ///
    /// The caller must ensure the parameters are in bounds, meaning:
    /// - If using the slice as initialized data, `start + len < self.init`.
    /// - If using the slice as uninitialized data, `start + len < self.size`.
    #[track_caller]
    #[inline]
    pub const unsafe fn get_slice_ptr_unchecked(&self, start: usize, len: usize) -> NonNull<[T]> {
        NonNull::slice_from_raw_parts(self.get_ptr_unchecked(start), len)
    }

    /// Gets a reference to a portion of the buffer.
    ///
    /// # Safety
    ///
    /// The caller must ensure the parameters are in bounds, meaning:
    /// - If using the slice as initialized data, `start + len < self.init`.
    /// - If using the slice as uninitialized data, `start + len < self.size`.
    #[track_caller]
    #[inline]
    pub const unsafe fn get_slice_unchecked(&self, start: usize, len: usize) -> &[T] {
        unsafe { &*self.get_slice_ptr_unchecked(start, len).as_ptr() }
    }

    /// Gets a mutable reference to a portion of the buffer.
    ///
    /// # Safety
    ///
    /// The caller must ensure the parameters are in bounds, meaning:
    /// - If using the slice as initialized data, `start + len < self.init`.
    /// - If using the slice as uninitialized data, `start + len < self.size`.
    #[track_caller]
    #[inline]
    pub const unsafe fn get_slice_mut_unchecked(&mut self, start: usize, len: usize) -> &mut [T] {
        unsafe { &mut *self.get_slice_ptr_unchecked(start, len).as_ptr() }
    }

    /// Reserves space for `additional` elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    pub fn reserve(&mut self, additional: usize) -> Result<(), AllocError> {
        unsafe {
            self.set_size_unchecked(self.size + additional)?;
        }
        Ok(())
    }

    /// Shrinks the vector's capacity to fit only as many elements as it has.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
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
    #[track_caller]
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
    /// The caller must ensure that `self.init < new_size`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    pub unsafe fn set_size_unchecked(&mut self, new_size: usize) -> Result<(), AllocError> {
        if new_size == self.size {
            return Ok(());
        }
        let new_buf = self.alloc.alloc_slice::<T>(new_size)?.cast();
        if self.buf != NonNull::dangling() {
            self.buf.copy_to_nonoverlapping(new_buf, self.init);
            self.alloc.dealloc_n(self.buf, self.size);
        }
        self.buf = new_buf;
        self.size = new_size;
        Ok(())
    }

    /// Destructor to drop all initialized elements and deallocate the buffer.
    #[track_caller]
    #[inline]
    pub fn drop_and_dealloc(self) {
        if self.buf != NonNull::dangling() {
            unsafe {
                NonNull::<[T]>::slice_from_raw_parts(self.buf.cast::<T>(), self.init)
                    .drop_in_place();
                self.alloc.dealloc_n(self.buf, self.size);
            }
        }
    }

    /// Destructor to drop all initialized elements, zero the allocated memory, and deallocate the
    /// buffer.
    #[track_caller]
    #[inline]
    pub fn drop_zero_and_dealloc(self) {
        if self.buf != NonNull::dangling() {
            unsafe {
                NonNull::<[MaybeUninit<T>]>::slice_from_raw_parts(
                    self.buf.cast::<MaybeUninit<T>>(),
                    self.init,
                )
                .drop_in_place();
                self.buf.as_ptr().write_bytes(0, self.size);
                self.alloc.dealloc_n(self.buf, self.size);
            }
        }
    }

    // TD: make sure this doesn't cause any issues elsewhere (like with drop methods or other
    //  deallocations)

    /// Drops all initialized elements and deallocates the buffer.
    #[track_caller]
    #[inline]
    pub fn reset(&mut self) {
        if self.buf != NonNull::dangling() {
            unsafe {
                NonNull::<[MaybeUninit<T>]>::slice_from_raw_parts(
                    self.buf.cast::<MaybeUninit<T>>(),
                    self.init,
                )
                .drop_in_place();
                self.alloc.dealloc_n(self.buf, self.size);
                self.init = 0;
                self.size = 0;
                self.buf = NonNull::dangling();
            }
        }
    }

    /// Drops all initialized elements, zeroes allocated memory, and deallocates the buffer.
    #[track_caller]
    #[inline]
    pub fn reset_zero(&mut self) {
        if self.buf != NonNull::dangling() {
            unsafe {
                NonNull::<[MaybeUninit<T>]>::slice_from_raw_parts(
                    self.buf.cast::<MaybeUninit<T>>(),
                    self.init,
                )
                .drop_in_place();
                self.buf.as_ptr().write_bytes(0, self.size);
                self.alloc.dealloc_n(self.buf, self.size);
                self.init = 0;
                self.size = 0;
                self.buf = NonNull::dangling();
            }
        }
    }

    /// Gets a pointer to the initialized portion of the buffer.
    #[inline]
    pub const fn as_slice_ptr(&self) -> NonNull<[T]> {
        NonNull::slice_from_raw_parts(self.buf, self.init)
    }

    /// Gets a reference to the initialized portion of the buffer.
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.buf.as_ptr(), self.init) }
    }

    /// Gets a mutable reference to the initialized portion of the buffer.
    #[inline]
    pub const fn as_slice_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.buf.as_ptr(), self.init) }
    }

    /// Gets a pointer to the entire buffer.
    #[inline]
    pub const fn as_uninit_slice_ptr(&self) -> NonNull<[MaybeUninit<T>]> {
        NonNull::slice_from_raw_parts(self.buf.cast::<MaybeUninit<T>>(), self.size)
    }

    /// Gets a reference to the entire buffer.
    #[inline]
    pub const fn as_uninit_slice(&self) -> &[MaybeUninit<T>] {
        unsafe { slice::from_raw_parts(self.buf.as_ptr().cast(), self.size) }
    }

    /// Gets a mutable reference to the entire buffer.
    #[inline]
    pub const fn as_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<T>] {
        unsafe { slice::from_raw_parts_mut(self.buf.as_ptr().cast(), self.size) }
    }

    /// Gets a pointer to the initialized portion of the buffer if it exists. Otherwise, gets an
    /// uninitialized pointer to the entire buffer.
    ///
    /// # Errors
    ///
    /// Returns `Err(uninit_ptr)` if there are no initialized elements in the buffer.
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

    /// Gets a reference to the initialized portion of the buffer if it exists. Otherwise, gets an
    /// uninitialized reference to the entire buffer.
    ///
    /// # Errors
    ///
    /// Returns `Err(uninit_ptr)` if there are no initialized elements in the buffer.
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

    /// Gets a mutable reference to the initialized portion of the buffer if it exists. Otherwise,
    /// gets an uninitialized mutable reference to the entire buffer.
    ///
    /// # Errors
    ///
    /// Returns `Err(uninit_ptr)` if there are no initialized elements in the buffer.
    #[inline]
    pub const fn try_as_slice_mut(&mut self) -> Result<&mut [T], Option<&mut [MaybeUninit<T>]>> {
        if self.init != 0 {
            Ok(self.as_slice_mut())
        } else if self.size != 0 {
            Err(Some(self.as_uninit_slice_mut()))
        } else {
            Err(None)
        }
    }

    /// Gets a reference to the buffer as a [`Buf`].
    pub const fn as_buf(&self) -> Buf<'_, T> {
        Buf {
            buf: self.as_uninit_slice(),
            init: self.init,
        }
    }

    /// Gets a reference to the buffer as a [`Buf`].
    ///
    /// The data will be considered unowned after this operation.
    pub fn into_buf<'s>(self) -> Buf<'s, T> {
        let (buf, init, size, _) = self.into_raw_parts();
        Buf {
            buf: unsafe { slice::from_raw_parts(buf.as_ptr().cast(), size) },
            init,
        }
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
        self
    }
}

impl<T, A: Alloc> AsMut<[T]> for OwnedBuf<T, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
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
    fn from(owned: &'s OwnedBuf<T, A>) -> Self {
        Buf::from(unsafe { &*(owned.as_uninit_slice_ptr().as_ptr() as *mut [T]) })
    }
}

impl<'s, T, A: Alloc> From<&'s mut OwnedBuf<T, A>> for Buf<'s, T> {
    #[inline]
    fn from(owned: &'s mut OwnedBuf<T, A>) -> Self {
        Buf::from(unsafe { &*(owned.as_uninit_slice_ptr().as_ptr() as *mut [T]) })
    }
}

impl<T, A: Alloc> Borrow<[T]> for OwnedBuf<T, A> {
    fn borrow(&self) -> &[T] {
        self
    }
}

impl<T, A: Alloc> Borrow<[MaybeUninit<T>]> for OwnedBuf<T, A> {
    fn borrow(&self) -> &[MaybeUninit<T>] {
        self.as_uninit_slice()
    }
}

impl<T, A: Alloc> BorrowMut<[T]> for OwnedBuf<T, A> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, A: Alloc> BorrowMut<[MaybeUninit<T>]> for OwnedBuf<T, A> {
    fn borrow_mut(&mut self) -> &mut [MaybeUninit<T>] {
        self.as_uninit_slice_mut()
    }
}

// TODO: improve this with specialization
impl<T: Clone, A: Alloc + Default> From<&[T]> for OwnedBuf<T, A> {
    #[track_caller]
    #[inline]
    fn from(slice: &[T]) -> OwnedBuf<T, A> {
        Buf::from(slice)
            .clone_into_owned_in(A::default())
            .expect("`<From<&[T]>>::from` failed")
    }
}

impl<T: Clone, A: Alloc + Default> From<&mut [T]> for OwnedBuf<T, A> {
    #[track_caller]
    #[inline]
    fn from(slice: &mut [T]) -> OwnedBuf<T, A> {
        OwnedBuf::from(&*slice)
    }
}

/// An unowned buffer of multiple `T`.
pub struct Buf<'s, T> {
    /// The buffer.
    pub buf: &'s [MaybeUninit<T>],
    /// The count of initialized elements in the buffer.
    pub init: usize,
}

impl<'s, T> From<&'s [T]> for Buf<'s, T> {
    #[inline]
    fn from(elems: &'s [T]) -> Buf<'s, T> {
        Buf {
            buf: unsafe { &*(ptr::from_ref(elems) as *const [MaybeUninit<T>]) },
            init: elems.len(),
        }
    }
}

impl<'s, T> From<&'s mut [T]> for Buf<'s, T> {
    #[inline]
    fn from(value: &'s mut [T]) -> Buf<'s, T> {
        Buf::from(&*value)
    }
}

impl<T> Deref for Buf<'_, T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { slice::from_raw_parts(ptr::from_ref(self.buf).cast(), self.init) }
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
    #[track_caller]
    #[inline]
    pub fn clone_into_owned(&self) -> Result<OwnedBuf<T>, AllocError>
    where
        T: Clone,
    {
        self.clone_into_owned_in(DefaultAlloc)
    }

    /// Creates a new owned buffer with a size equivalent to the contained slice, and copies all
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

    /// Creates a new owned buffer with a size equivalent to the contained slice, and clones all
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
    /// allocator, then clones all initialized elements into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    pub fn clone_into_owned_in<A: Alloc>(&self, alloc: A) -> Result<OwnedBuf<T, A>, AllocError>
    where
        T: Clone,
    {
        let (buf, _, size, alloc) = OwnedBuf::new_in(self.buf.len(), alloc)?.into_raw_parts();
        let mut buf = SliceAllocGuard::new(buf, &alloc, size);
        for i in 0..self.init {
            unsafe {
                buf.init(self.buf.get_unchecked(i).assume_init_ref().clone())
                    .unwrap_unchecked();
            }
        }
        Ok(OwnedBuf {
            buf: buf.release().cast::<T>(),
            init: self.init,
            size,
            alloc,
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
    /// allocator, then clones all initialized elements into it. This method has no `T: Copy` bound.
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
        for i in 0..self.init {
            buf.add(i).write(ptr::read(
                ptr::from_ref(self.buf.get_unchecked(i)).cast::<T>(),
            ));
        }
        Ok(OwnedBuf {
            buf,
            init: self.init,
            size,
            alloc,
        })
    }

    /// Assumes that this borrowed [`Buf`] is not currently owned, and thus can be directly
    /// converted back into an [`OwnedBuf`].
    ///
    /// # Safety
    ///
    /// The contained elements must be unowned.
    #[track_caller]
    #[inline]
    pub const unsafe fn into_owned<A: Alloc>(self, alloc: A) -> OwnedBuf<T, A> {
        let Buf { init, buf: elems } = self;
        OwnedBuf {
            buf: NonNull::from_ref(elems).cast::<T>(),
            init,
            size: elems.len(),
            alloc,
        }
    }
}
