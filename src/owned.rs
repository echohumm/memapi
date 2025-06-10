use crate::{
    Alloc, AllocError,
    owned::VariableError::{Hard, Soft},
};
use core::{error::Error, fmt::{self, Debug, Display, Formatter}, mem::{MaybeUninit, transmute}, ops::{Deref, DerefMut}, ptr, ptr::{NonNull, replace}, slice};
use core::mem::{forget, ManuallyDrop};

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
pub struct OwnedBuf<T, A: Alloc> {
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

impl<T, A: Alloc> OwnedBuf<T, A> {
    /// Creates a new owned buffer of `T` with the given length, in the given allocator.
    ///
    /// # Errors
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    pub fn new(len: usize, alloc: A) -> Result<OwnedBuf<T, A>, AllocError> {
        Ok(OwnedBuf {
            buf: alloc.alloc_slice::<T>(len)?.cast(),
            init: 0,
            size: len,
            alloc,
        })
    }

    /// Creates a new, unallocated owned buffer of `T`, set to use the given allocator for future
    /// allocations.
    #[inline]
    pub const fn new_unallocated(alloc: A) -> OwnedBuf<T, A> {
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
        (me.buf, me.init, me.size, unsafe { ptr::read(&me.alloc) })
    }

    /// Creates a new owned buffer of `T` from the given parts.
    #[inline]
    pub const fn from_raw_parts(
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
            src.copy_from_nonoverlapping(src.add(1), self.init - idx - 1);
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
    /// - `Err(Ok(val))` if the index is out of bounds.
    /// - `Err(Err((alloc_err, val)))` if the index is in bounds, but the vector is full and
    ///   allocation for an expansion fails.
    ///
    /// `alloc_err` may be:
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    pub fn try_insert_grow(
        &mut self,
        idx: usize,
        val: T,
    ) -> Result<(), VariableError<T, (AllocError, T)>> {
        if idx > self.init {
            return Err(Soft(val));
        }
        match self.expand_to_fit(self.init + 1) {
            Ok(()) => {}
            Err(e) => return Err(Hard((e, val))),
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
    /// - `Err(Ok(val))` if the index is out of bounds or there is no space for the element.
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

    // TODO: slice removal, also extending
    /// Placeholder
    pub fn try_insert_slice_grow<A2: Alloc>(
        &mut self,
        idx: usize,
        slice: OwnedBuf<T, A2>,
    ) -> Result<(), VariableError<OwnedBuf<T, A2>, (AllocError, OwnedBuf<T, A2>)>> {
        if idx > self.init {
            return Err(Soft(slice));
        }
        match self.expand_to_fit(self.init + slice.len()) {
            Ok(()) => {}
            Err(e) => return Err(Hard((e, slice))),
        }

        unsafe {
            self.insert_slice_unchecked(idx, slice);
        }

        Ok(())
    }

    /// Placeholder
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

    /// Placeholder
    pub unsafe fn insert_slice_unchecked<A2: Alloc>(&mut self, idx: usize, slice: OwnedBuf<T, A2>) {
        // pointer to initialized elements
        let src = slice.as_slice_ptr().as_ptr();
        // destination of the slice
        let dst = self.get_ptr_unchecked(idx);
        // shift elements over to make space as necessary
        if idx != self.init {
            dst.copy_to_nonoverlapping(dst.add(src.len()), self.init - idx);
        }
        // write in the elements
        self.buf
            .as_ptr()
            .add(idx)
            .copy_from_nonoverlapping(src.cast::<T>(), src.len());
        // deallocate the original buffer
        slice
            .alloc
            .dealloc_n(NonNull::new_unchecked(src.cast::<T>()), slice.size);
        // update initialized element count
        self.init += src.len();
    }

    // /// Placeholder
    // #[inline]
    // pub const fn try_replace_slice<A2: Alloc>(
    //     &mut self,
    //     idx: usize,
    //     slice: OwnedBuf<T, A2>,
    // ) -> Result<OwnedBuf<T, A>, OwnedBuf<T, A2>> where A: Clone {
    //     todo!()
    // }
    //
    // /// Placeholder
    // #[inline]
    // pub fn replace_slice_grow<A2: Alloc>(
    //     &mut self,
    //     idx: usize,
    //     slice: OwnedBuf<T, A2>,
    // ) -> Result<OwnedBuf<T, A>, AllocError> where A: Clone {
    //     self.expand_to_fit(self.init + slice.init)?;
    //     let replaced = todo!();
    //     unsafe {
    //         self.replace_slice_unchecked(idx, slice);
    //     }
    //     Ok(())
    // }
    //
    // /// Placeholder
    // #[inline]
    // pub const unsafe fn replace_slice_unchecked<A2: Alloc>(
    //     &mut self,
    //     idx: usize,
    //     slice: OwnedBuf<T, A2>,
    //     replaced: usize,
    // ) -> OwnedBuf<T, A>
    // where
    //     A: Clone,
    // {
    //     let src = slice.as_slice_ptr().as_ptr();
    //     let dst = self.get_ptr_unchecked(idx);
    //
    //     todo!()
    // }

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
