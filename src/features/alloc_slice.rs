use crate::{
    error::AllocError,
    grow,
    helpers::{
        alloc_slice, dealloc_n, layout_or_sz_align, nonnull_slice_from_raw_parts,
        nonnull_slice_len, slice_ptr_from_raw_parts, SliceAllocGuard, TRUNC_LGR,
    },
    ralloc, shrink,
    type_props::{PtrProps, SizedProps},
    Alloc, AllocPattern,
};
use core::{
    alloc::Layout,
    mem::MaybeUninit,
    ptr::{self, NonNull},
};
// TODO: slice growth and realloc with copying and cloning.
// MAYBEDO: reduce duplication

macro_rules! realloc {
    (
        $fun:ident,
        $self:ident,$ptr:ident,
        $len:expr,
        $new_len:expr,
        $ty:ty
        $(,$pat:ident$(($val:ident))?)?)
    => {
		realloc!(
            fn(usize) -> u8,
            $fun,
            $self,
            $ptr,
            $len,
            $new_len,
            $ty $(,$pat$(($val))?)?
        )
	};
    ($f:ty,
        $fun:ident,
        $self:ident,
        $ptr:ident,
        $len:expr,
        $new_len:expr,
        $ty:ty
        $(,$pat:ident$(($val:ident))?)?
    )
    => {
        $fun(
            $self,
            $ptr.cast(),
            Layout::from_size_align_unchecked($len * <$ty>::SZ, <$ty>::ALIGN),
            layout_or_sz_align::<$ty>($new_len)
                .map_err(|(sz, aln)| AllocError::LayoutError(sz, aln))?,
            $(AllocPattern::<$f>::$pat$(($val))?)?
        )
        .map(NonNull::cast)
    }
}

/// Small helper to fill new elements of a grown slice using a predicate.
unsafe fn fill_new_elems_with<T, A: Alloc + ?Sized, F: Fn(usize) -> T>(
    a: &A,
    p: NonNull<T>,
    len: usize,
    new_len: usize,
    f: F,
) -> NonNull<T> {
    let mut guard = SliceAllocGuard::new(p, a, new_len);
    guard.set_init(len);
    for i in len..new_len {
        guard.init_unchecked(f(i));
    }
    guard.release_first()
}

unsafe fn resize_init<
    T,
    I: Fn(NonNull<[T]>, &mut usize),
    A: Alloc + ?Sized,
    F: Fn(&A, NonNull<T>, usize, usize) -> Result<NonNull<T>, AllocError>,
>(
    a: &A,
    ptr: NonNull<T>,
    len: usize,
    new_len: usize,
    f: F,
    init: I,
) -> Result<NonNull<T>, AllocError> {
    match f(a, ptr, len, new_len) {
        Ok(p) => {
            let mut guard = SliceAllocGuard::new(p, a, new_len);
            guard.set_init(len);
            init(guard.get_uninit_part(), &mut guard.init);
            Ok(guard.release_first())
        }
        Err(e) => Err(e),
    }
}

/// Slice-specific extension methods for [`Alloc`], providing convenient functions for slice
/// allocator operations.
pub trait AllocSlice: Alloc {
    /// Attempts to allocate a block of memory for `len` instances of `T`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_slice<T>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
        alloc_slice(self, len, Self::alloc)
    }

    /// Attempts to allocate a zeroed block of memory for `len` instances of `T`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_slice_zeroed<T>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
        alloc_slice(self, len, Self::alloc_zeroed)
    }

    /// Allocates uninitialized memory for a slice of `T` and clones each element from `data` into
    /// it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if the slice is zero-sized.
    #[track_caller]
    #[inline]
    fn alloc_clone_slice_to<T: Clone>(&self, data: &[T]) -> Result<NonNull<[T]>, AllocError> {
        match self.alloc(unsafe { data.layout() }) {
            Ok(ptr) => Ok(unsafe {
                let mut guard = SliceAllocGuard::new(ptr.cast(), self, data.len());
                for elem in data {
                    guard.init_unchecked(elem.clone());
                }
                guard.release()
            }),
            Err(e) => Err(e),
        }
    }

    /// Allocates uninitialized memory for a slice of `T` and copies each element from `data` into
    /// it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if the slice is zero-sized.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_copy_slice_to<T: Copy>(&self, data: &[T]) -> Result<NonNull<[T]>, AllocError> {
        unsafe { self.alloc_copy_slice_to_unchecked(data) }
    }

    /// Allocates uninitialized memory for a slice of `T` and copies each element from `data` into
    /// it. This method does not require `T: Copy`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if the slice is zero-sized.
    ///
    /// # Safety
    ///
    /// The caller must ensure it is safe to copy the elements in `data`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_copy_slice_to_unchecked<T>(
        &self,
        data: &[T],
    ) -> Result<NonNull<[T]>, AllocError> {
        match self.alloc(data.layout()) {
            Ok(ptr) => Ok({
                let p = ptr.cast::<T>();
                ptr::copy_nonoverlapping(data as *const [T] as *const T, p.as_ptr(), data.len());

                nonnull_slice_from_raw_parts(p, data.len())
            }),
            Err(e) => Err(e),
        }
    }

    /// Allocates uninitialized memory for a `[T]` of length `len` and fills each element with the
    /// result of `f(elem_idx)` under a guard to drop and deallocate on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_slice_with<T, F: Fn(usize) -> T>(
        &self,
        len: usize,
        f: F,
    ) -> Result<NonNull<[T]>, AllocError> {
        match self.alloc(
            layout_or_sz_align::<T>(len).map_err(|(sz, aln)| AllocError::LayoutError(sz, aln))?,
        ) {
            Ok(ptr) => Ok(unsafe {
                let mut guard = SliceAllocGuard::new(ptr.cast(), self, len);
                for i in 0..len {
                    guard.init_unchecked(f(i));
                }
                guard.release()
            }),
            Err(e) => Err(e),
        }
    }

    /// Allocates uninitialized memory for a `[T]` of length `len` and initializes it using `init`.
    ///
    /// `init` receives a pointer to the entire slice and a mutable reference to an initialized
    /// element counter.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    ///
    /// # Safety
    ///
    /// The caller must ensure the initialized element counter will be the same as the slice's
    /// length after `init` finishes, and that at any time `init` may panic, the counter will be
    /// accurate.
    #[track_caller]
    #[inline]
    unsafe fn alloc_slice_init<T, I: Fn(NonNull<[T]>, &mut usize)>(
        &self,
        init: I,
        len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        let mut guard = SliceAllocGuard::new(self.alloc_slice::<T>(len)?.cast::<T>(), self, len);
        init(guard.get_full(), &mut guard.init);
        Ok(guard.release())
    }

    /// Allocates uninitialized memory for a `[T]` of length `len` and fills each element
    /// with `T`'s default value.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_slice_default<T: Default>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
        self.alloc_slice_with(len, |_| T::default())
    }

    /// Drops `init` elements from a partially initialized slice and deallocates it.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, a valid `[T]` for `init` elements, and a valid `[MaybeUninit<T>]`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn drop_and_dealloc_uninit_slice<T>(&self, ptr: NonNull<[MaybeUninit<T>]>, init: usize) {
        ptr::drop_in_place(slice_ptr_from_raw_parts(ptr.as_ptr() as *mut T, init));
        self.dealloc(ptr.cast::<u8>(), ptr.layout());
    }

    /// Drops `init` elements from a partially initialized slice, then zeroes and deallocates its
    /// memory.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and a valid `T`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn drop_zero_and_dealloc_uninit_slice<T>(
        &self,
        slice: NonNull<[MaybeUninit<T>]>,
        init: usize,
    ) {
        ptr::drop_in_place(slice_ptr_from_raw_parts(slice.as_ptr() as *mut T, init));
        ptr::write_bytes(slice.as_ptr() as *mut T, 0, nonnull_slice_len(slice));
        self.dealloc(slice.cast::<u8>(), slice.layout());
    }

    /// Allocates memory for a slice of uninitialized `T` with the given length and returns a
    /// [`SliceAllocGuard`] around it to ensure proper destruction and deallocation on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_slice_guard<T>(
        &'_ self,
        len: usize,
    ) -> Result<SliceAllocGuard<'_, T, Self>, AllocError> {
        match self.alloc_slice::<T>(len) {
            Ok(ptr) => Ok(SliceAllocGuard::new(ptr.cast(), self, len)),
            Err(e) => Err(e),
        }
    }

    /// Grows a slice to a new length.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    // Safety #2 implies that `len` must be a valid length for the slice (which is required because
    // we use from_size_align_unchecked)
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(grow, self, ptr, len, new_len, T, None)
    }

    /// Grows a slice to a new length, zeroing any newly allocated bytes.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow_slice_zeroed<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice_zeroed(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length, zeroing any newly allocated bytes.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow_raw_slice_zeroed<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(grow, self, ptr, len, new_len, T, Zero)
    }

    /// Grows a slice to a new length and fills each new element with the result of `f(elem_idx)`
    /// under a guard to drop and deallocate on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
    #[inline]
    unsafe fn grow_slice_with<T, F: Fn(usize) -> T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        f: F,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice_with(slice.cast::<T>(), nonnull_slice_len(slice), new_len, f)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length, then fills each new element with the result of `f(elem_idx)` under a guard
    /// to drop and deallocate on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
    #[inline]
    unsafe fn grow_raw_slice_with<T, F: Fn(usize) -> T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        f: F,
    ) -> Result<NonNull<T>, AllocError> {
        match self.grow_raw_slice(ptr, len, new_len) {
            Ok(p) => Ok(fill_new_elems_with(&self, p, len, new_len, f)),
            Err(e) => Err(e),
        }
    }

    /// Grows a `[T]` to a new length and initializes the new elements using `init`.
    ///
    /// `init` receives a pointer to the entire slice and a mutable reference to an initialized
    /// element counter.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be accurate.
    #[track_caller]
    #[inline]
    unsafe fn grow_slice_init<T, I: Fn(NonNull<[T]>, &mut usize)>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        init: I,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice_init(slice.cast::<T>(), nonnull_slice_len(slice), new_len, init)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a `[T]` to a new length given the pointer to its first element, current length, and
    /// requested length, then initializes the new elements using `init`.
    ///
    /// `init` receives a pointer to the entire slice and a mutable reference to an initialized
    /// element counter.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be accurate.
    #[track_caller]
    #[inline]
    unsafe fn grow_raw_slice_init<T, I: Fn(NonNull<[T]>, &mut usize)>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        init: I,
    ) -> Result<NonNull<T>, AllocError> {
        resize_init(
            self,
            ptr,
            len,
            new_len,
            |a, p, len, new| unsafe { a.grow_raw_slice(p, len, new) },
            init,
        )
    }

    /// Grows a `[T]` to a new length and fills each new element with `T`'s default value.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
    #[inline]
    unsafe fn grow_slice_default<T: Default>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice_default(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a `[T]` to a new length given the pointer to its first element, current length, and
    /// requested length, then fills each new element with `T`'s default value.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
    #[inline]
    unsafe fn grow_raw_slice_default<T: Default>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        self.grow_raw_slice_with(ptr, len, new_len, |_| T::default())
    }

    /// Shrinks a slice to a new length without dropping any removed elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_len > slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn shrink_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.shrink_raw_slice(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Shrinks a slice to a new length given the pointer to its first element, current length, and
    /// requested length. This does not drop any removed elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_len > len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn shrink_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(shrink, self, ptr, len, new_len, T)
    }

    /// Shrinks a slice to a new length, dropping any removed elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other("attempted to truncate a slice to a larger size")`] if
    ///   `new_len > slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn truncate_slice<T>(
        &self,
        slice: NonNull<[T]>,
        init: usize,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.truncate_raw_slice(slice.cast::<T>(), nonnull_slice_len(slice), init, new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Shrinks a slice to a new length given the pointer to its first element, current length, and
    /// requested length. This drops any removed elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other("attempted to truncate a slice to a larger size")`] if
    ///   `new_len > len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn truncate_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        init: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        if new_len > len {
            return Err(AllocError::Other(TRUNC_LGR));
        }

        if new_len < init {
            let to_drop = init - new_len;
            ptr::drop_in_place(slice_ptr_from_raw_parts(ptr.as_ptr().add(new_len), to_drop));
        }

        self.shrink_raw_slice(ptr, len, new_len)
    }

    /// Reallocates a slice to a new length without dropping any removed elements.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_slice(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink. This
    /// does not drop any removed elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(ralloc, self, ptr, len, new_len, T, None)
    }

    /// Reallocates a slice to a new length without dropping any removed elements.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink.
    ///
    /// Any newly allocated bytes will be zeroed.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc_slice_zeroed<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_slice_zeroed(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink. This
    /// does not drop any removed elements.
    ///
    /// Any newly allocated bytes will be zeroed.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc_raw_slice_zeroed<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(ralloc, self, ptr, len, new_len, T, Zero)
    }

    /// Reallocates a slice to a new length and fills each new element with the result of
    /// `f(elem_idx)`.
    ///
    /// On grow, preserves all existing elements and fills new ones by calling `f(i)`.
    /// On shrink, truncates to `new_len` elements without dropping removed elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
    #[inline]
    unsafe fn realloc_slice_with<T, F: Fn(usize) -> T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        f: F,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_slice_with(slice.cast::<T>(), nonnull_slice_len(slice), new_len, f)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length, filling any newly allocated elements with the result of `f(elem_idx)`
    /// under a guard to drop and deallocate on panic.
    ///
    /// On grow, preserves all existing elements and fills new ones by calling `f(i)`.
    /// On shrink, truncates to `new_len` elements without dropping removed elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
    #[inline]
    unsafe fn realloc_raw_slice_with<T, F: Fn(usize) -> T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        f: F,
    ) -> Result<NonNull<T>, AllocError> {
        match self.realloc_raw_slice(ptr, len, new_len) {
            Ok(p) => {
                if new_len > len {
                    Ok(fill_new_elems_with(&self, p, len, new_len, f))
                } else {
                    Ok(p)
                }
            }
            Err(e) => Err(e),
        }
    }

    /// Reallocates a `[T]` to a new length and initializes the new elements using `init`.
    ///
    /// On grow, preserves existing elements and calls `init` on the newly allocated sub-slice.
    /// On shrink, truncates to `new_len` without dropping removed elements.
    ///
    /// `init` receives a pointer to the new elements of the slice and a mutable reference to an
    /// initialized element counter.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be accurate.
    #[track_caller]
    #[inline]
    unsafe fn realloc_slice_init<T, I: Fn(NonNull<[T]>, &mut usize)>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        init: I,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_slice_init(slice.cast::<T>(), nonnull_slice_len(slice), new_len, init)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a `[T]` to a new length given the pointer to its first element, current length,
    /// and requested length, then initializes the new elements using `init`.
    ///
    /// On grow, preserves existing elements and invokes `init` on the sub-slice of newly allocated
    /// elements. On shrink, truncates to `new_len` without dropping removed elements.
    ///
    /// `init` receives a pointer to the new elements of the slice and a mutable reference to an
    /// initialized element counter.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be accurate.
    #[track_caller]
    #[inline]
    unsafe fn realloc_raw_slice_init<T, I: Fn(NonNull<[T]>, &mut usize)>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        init: I,
    ) -> Result<NonNull<T>, AllocError> {
        resize_init(
            self,
            ptr,
            len,
            new_len,
            |a, p, len, new| unsafe { a.realloc_raw_slice(p, len, new) },
            init,
        )
    }

    /// Reallocates a slice to a new length and fills each new element with `T`'s default value.
    ///
    /// On grow, preserves all existing elements and fills new ones by calling `T::default()`.
    /// On shrink, truncates to `new_len` elements without dropping removed elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
    #[inline]
    unsafe fn realloc_slice_default<T: Default>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_slice_default(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length, then fills each new element with `T`'s default value.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
    #[inline]
    unsafe fn realloc_raw_slice_default<T: Default>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        self.realloc_raw_slice_with(ptr, len, new_len, |_| T::default())
    }

    /// Deallocates a previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `n` must be the exact number of `T` held in that block.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) {
        dealloc_n(self, ptr, n);
    }

    /// Zeroes and deallocates `n` elements at the given pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and a valid `T`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zero_and_dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) {
        ptr::write_bytes(ptr.as_ptr(), 0, n);
        self.dealloc_n(ptr, n);
    }

    /// Drops the data at a pointer and deallocates its previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and contain `n` valid `T`.
    /// - `n` must be the exact number of `T` held in that block.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn drop_and_dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) {
        ptr::drop_in_place(slice_ptr_from_raw_parts(ptr.as_ptr(), n));
        self.dealloc_n(ptr, n);
    }
}

impl<A: Alloc + ?Sized> AllocSlice for A {}

#[cfg(feature = "alloc_ext")]
/// Slice-specific extension methods for [`AllocExt`](crate::AllocExt), providing
/// extended convenient functions for slice allocator operations.
pub trait AllocSliceExt: AllocSlice + crate::AllocExt {
    /// Attempts to allocate a block of memory for `len` instances of `T`, filled with bytes
    /// initialized to `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_slice_filled<T>(&self, len: usize, n: u8) -> Result<NonNull<[T]>, AllocError> {
        let layout = layout_or_sz_align::<T>(len)
            .map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        self.alloc_filled(layout, n)
            .map(|ptr| nonnull_slice_from_raw_parts(ptr.cast(), len))
    }

    /// Attempts to allocate a block of memory for `len` instances of `T` and
    /// fill it by calling `pattern(i)` for each byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_slice_patterned<T, F: Fn(usize) -> u8 + Clone>(
        &self,
        len: usize,
        pattern: F,
    ) -> Result<NonNull<[T]>, AllocError> {
        let layout = layout_or_sz_align::<T>(len)
            .map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        self.alloc_patterned(layout, pattern)
            .map(|ptr| nonnull_slice_from_raw_parts(ptr.cast(), len))
    }

    /// Grows a slice to a new length, filling any newly allocated bytes with `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow_slice_filled<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        n: u8,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice_filled(slice.cast::<T>(), nonnull_slice_len(slice), new_len, n)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length, filling any newly allocated bytes with `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow_raw_slice_filled<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        n: u8,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(grow, self, ptr, len, new_len, T, All(n))
    }

    /// Grows a slice to a new length, filling any newly allocated bytes by calling `pattern(i)`
    /// for each new byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
    #[inline]
    unsafe fn grow_slice_patterned<T, F: Fn(usize) -> u8 + Clone>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        pattern: F,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice_patterned(
            slice.cast::<T>(),
            nonnull_slice_len(slice),
            new_len,
            pattern.clone(),
        )
        .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length, filling any newly allocated bytes by calling `pattern(i)` for each new
    /// byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
    #[inline]
    unsafe fn grow_raw_slice_patterned<T, F: Fn(usize) -> u8 + Clone>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        pattern: F,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(F, grow, self, ptr, len, new_len, T, Fn(pattern))
    }

    /// Reallocates a slice to a new length, filling any newly allocated bytes with `n`.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc_slice_filled<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        n: u8,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_slice_filled(slice.cast::<T>(), nonnull_slice_len(slice), new_len, n)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length, filling any newly allocated bytes with `n`.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc_raw_slice_filled<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        n: u8,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(ralloc, self, ptr, len, new_len, T, All(n))
    }

    /// Reallocates a slice to a new length, filling any newly allocated bytes by calling
    /// `pattern(i)` for each new byte index `i`.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
    #[inline]
    unsafe fn realloc_slice_patterned<T, F: Fn(usize) -> u8 + Clone>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        pattern: F,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_slice_patterned(
            slice.cast::<T>(),
            nonnull_slice_len(slice),
            new_len,
            pattern.clone(),
        )
        .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length, filling any newly allocated bytes by calling `pattern(i)` for each new
    /// byte index `i`.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
    #[inline]
    unsafe fn realloc_raw_slice_patterned<T, F: Fn(usize) -> u8 + Clone>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        pattern: F,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(F, ralloc, self, ptr, len, new_len, T, Fn(pattern))
    }
}

impl<A: AllocSlice + ?Sized> AllocSliceExt for A {}
