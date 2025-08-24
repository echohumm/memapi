use {
    crate::{
        Alloc,
        AllocPattern,
        Layout,
        data::type_props::SizedProps,
        error::{AllocError, ArithOp},
        grow,
        helpers::{
            checked_op_panic,
            layout_or_err,
            nonnull_slice_from_raw_parts,
            nonnull_slice_len
        },
        ralloc,
        shrink
    },
    core::ptr::NonNull
};

// TODO: review usage and make small semantic adjustments, like making functions take
//  [MaybeUninit<T>] and an extra `init` count instead of just [T] for ease of use.
// TODO: check docs like did with alloc_ext

#[cfg(feature = "alloc_ext")]
const INSUF_GROW_SRC: AllocError =
    AllocError::Other("source slice length is insufficient to fill new elements");

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
    => {{
        $fun(
            $self,
            $ptr.cast(),
            // SAFETY: we assume the original layout is valid as it was presumably used to allocate
            //  previously
            Layout::from_size_align_unchecked(<$ty>::SZ * $len, <$ty>::ALN),
            tri!(AllocError::InvalidLayout(layout_or_err::<$ty>($new_len))),
            $(AllocPattern::$pat$(($val))?)?
        )
        .map(NonNull::cast)
    }}
}

#[cfg(feature = "alloc_ext")]
/// Small helper to fill new elements of a grown slice using a predicate.
#[cfg_attr(miri, track_caller)]
unsafe fn fill_new_elems_with<T, A: Alloc + ?Sized, F: Fn(usize) -> T>(
    a: &A,
    p: NonNull<T>,
    len: usize,
    new_len: usize,
    f: F
) -> NonNull<T> {
    let mut guard = crate::helpers::SliceAllocGuard::new_with_init(p, a, len, new_len);

    for i in len..new_len {
        guard.init_unchecked(f(i));
    }
    guard.release_first()
}

/// Small helper to allocate a slice using a given allocation function.
#[cfg_attr(miri, track_caller)]
pub(crate) fn alloc_slice<
    T,
    A: Alloc + ?Sized,
    F: Fn(&A, Layout) -> Result<NonNull<u8>, AllocError>
>(
    a: &A,
    len: usize,
    alloc: F
) -> Result<NonNull<[T]>, AllocError> {
    alloc(a, tri!(AllocError::InvalidLayout(layout_or_err::<T>(len))))
        .map(|ptr| nonnull_slice_from_raw_parts(ptr.cast(), len))
}

/// Slice-specific extension methods for [`Alloc`], providing convenient functions for slice
/// allocator operations.
pub trait AllocSlice: Alloc {
    /// Attempts to allocate a block of memory for `len` instances of `T`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn salloc<T>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
        alloc_slice(self, len, Self::alloc)
    }

    /// Attempts to allocate a zeroed block of memory for `len` instances of `T`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zsalloc<T>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
        alloc_slice(self, len, Self::zalloc)
    }

    /// Deallocates a previously allocated block.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - point to a block of memory allocated using this allocator
    /// - be properly aligned
    #[cfg_attr(miri, track_caller)]
    unsafe fn dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) {
        // Here, we assume the layout is valid as it was presumably used to allocate previously.
        self.dealloc(
            ptr.cast(),
            Layout::from_size_align_unchecked(checked_op_panic(T::SZ, ArithOp::Mul, n), T::ALN)
        );
    }

    /// Grows a slice to a new length.
    ///
    /// # Safety
    ///
    /// `slice` must point to a slice allocated using this allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn sgrow<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    // Safety #2 implies that `len` must be a valid length for the slice (which is required because
    // we use from_size_align_unchecked)
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow_raw<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(grow, self, ptr, len, new_len, T, Uninitialized)
    }

    /// Grows a slice to a new length, zeroing any newly allocated bytes.
    ///
    /// # Safety
    ///
    /// `slice` must point to a slice allocated using this allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn zsgrow<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize
    ) -> Result<NonNull<[T]>, AllocError> {
        self.zgrow_raw(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length, zeroing any newly allocated bytes.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn zgrow_raw<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(grow, self, ptr, len, new_len, T, Zeroed)
    }

    /// Shrinks a slice to a new length without dropping any removed elements.
    ///
    /// # Safety
    ///
    /// `slice` must point to a slice allocated using this allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ShrinkLargerNewLayout`] if `new_len > slice.len()`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn shrink_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize
    ) -> Result<NonNull<[T]>, AllocError> {
        self.shrink_raw(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Shrinks a slice to a new length given the pointer to its first element, current length, and
    /// requested length. This doesn't drop any removed elements.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ShrinkLargerNewLayout`] if `new_len > len`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn shrink_raw<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(shrink, self, ptr, len, new_len, T)
    }

    /// Reallocates a slice to a new length without dropping any removed elements.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink.
    ///
    /// # Safety
    ///
    /// `slice` must point to a slice allocated using this allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    #[cfg_attr(miri, track_caller)]
    unsafe fn resalloc<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink. This
    /// doesn't drop any removed elements.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    #[cfg_attr(miri, track_caller)]
    unsafe fn realloc_raw<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(ralloc, self, ptr, len, new_len, T, Uninitialized)
    }

    /// Reallocates a slice to a new length without dropping any removed elements.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink.
    ///
    /// Any newly allocated bytes will be zeroed.
    ///
    /// # Safety
    ///
    /// `slice` must point to a slice allocated using this allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    #[cfg_attr(miri, track_caller)]
    unsafe fn rezsalloc<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize
    ) -> Result<NonNull<[T]>, AllocError> {
        self.rezalloc_raw(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink. This
    /// doesn't drop any removed elements.
    ///
    /// Any newly allocated bytes will be zeroed.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    #[cfg_attr(miri, track_caller)]
    unsafe fn rezalloc_raw<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(ralloc, self, ptr, len, new_len, T, Zeroed)
    }
}

impl<A: Alloc + ?Sized> AllocSlice for A {}

#[cfg(feature = "alloc_ext")]
#[allow(clippy::module_name_repetitions)]
/// Slice-specific extension methods for [`AllocExt`](crate::AllocExt), providing
/// extended convenient functions for slice allocator operations.
pub trait AllocSliceExt: AllocSlice + crate::AllocExt {
    /// Attempts to allocate a block of memory for `len` instances of `T`, filled with bytes
    /// initialized to `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    fn fsalloc<T>(&self, len: usize, n: u8) -> Result<NonNull<[T]>, AllocError> {
        alloc_slice(self, len, |a, layout| a.falloc(layout, n))
    }

    /// Allocates uninitialized memory for a slice of `T` and clones each element from `data` into
    /// it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if the slice is zero-sized.
    #[track_caller]
    fn salloc_clone<T: Clone>(&self, data: &[T]) -> Result<NonNull<[T]>, AllocError> {
        // SAFETY: `data` is a reference, which immediately fulfills the invariants of layout(); we
        //  just allocated the slice using `self` with space for at least `data.len()`
        //  elements
        unsafe {
            crate::helpers::alloc_then(
                self,
                crate::data::type_props::PtrProps::layout(&data),
                data,
                |p, data| {
                    let mut guard =
                        crate::helpers::SliceAllocGuard::new(p.cast(), self, data.len());
                    for elem in data {
                        guard.init_unchecked(elem.clone());
                    }
                    guard.release()
                }
            )
        }
    }

    /// Allocates uninitialized memory for a `[T]` of length `len` and fills each element with the
    /// result of `f(elem_idx)` under a guard to drop and deallocate on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    fn salloc_with<T, F: Fn(usize) -> T>(
        &self,
        len: usize,
        f: F
    ) -> Result<NonNull<[T]>, AllocError> {
        // SAFETY: we just allocated the slice using `self` with space for at least `len` elements
        crate::helpers::alloc_then(
            self,
            tri!(AllocError::InvalidLayout(layout_or_err::<T>(len))),
            f,
            |p, f| unsafe {
                let mut guard = crate::helpers::SliceAllocGuard::new(p.cast(), self, len);
                for i in 0..len {
                    guard.init_unchecked(f(i));
                }
                guard.release()
            }
        )
    }

    /// Grows a slice to a new length, filling any newly allocated bytes with `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    unsafe fn fsgrow<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        n: u8
    ) -> Result<NonNull<[T]>, AllocError> {
        self.fgrow_raw(slice.cast::<T>(), nonnull_slice_len(slice), new_len, n)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length, filling any newly allocated bytes with `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
    unsafe fn fgrow_raw<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        n: u8
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(grow, self, ptr, len, new_len, T, Filled(n))
    }

    /// Grows a slice to a new length and fills each new element with the result of `f(elem_idx)`
    /// under a guard to drop and deallocate on panic.
    ///
    /// # Safety
    ///
    /// `slice` must point to a slice allocated using this allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    #[track_caller]
    unsafe fn sgrow_with<T, F: Fn(usize) -> T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        f: F
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_with(slice.cast::<T>(), nonnull_slice_len(slice), new_len, f)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length, then fills each new element with the result of `f(elem_idx)` under a guard
    /// to drop and deallocate on panic.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    #[track_caller]
    unsafe fn grow_raw_with<T, F: Fn(usize) -> T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        f: F
    ) -> Result<NonNull<T>, AllocError> {
        match self.grow_raw(ptr, len, new_len) {
            Ok(p) => Ok(fill_new_elems_with(&self, p, len, new_len, f)),
            Err(e) => Err(e)
        }
    }

    /// Grows a slice to a new length and clones elements from `src` into the newly allocated
    /// region.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - `src` must contain at least `new_len - slice.len()` readable elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    /// - [`AllocError::Other`]`("source slice length is insufficient to fill new elements")` if
    ///   `src_len < new_len - len`.
    #[track_caller]
    unsafe fn sgrow_clone_from<T: Clone>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        src: NonNull<[T]>
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_clone_from(
            slice.cast::<T>(),
            nonnull_slice_len(slice),
            new_len,
            src.cast::<T>(),
            nonnull_slice_len(src)
        )
        .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length,
    /// and requested length, then clones elements from `src` into the newly allocated region.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    /// - `src` must contain at least `new_len - len` readable elements.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    /// - [`AllocError::Other`]`("source slice length is insufficient to fill new elements")` if
    ///   `src_len < new_len - len`.
    #[track_caller]
    unsafe fn grow_raw_clone_from<T: Clone>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,

        src: NonNull<T>,
        src_len: usize
    ) -> Result<NonNull<T>, AllocError> {
        if new_len == len {
            return Ok(ptr);
        }

        let to_add = new_len - len;
        if src_len < to_add {
            return Err(INSUF_GROW_SRC);
        }

        let mut guard = crate::helpers::SliceAllocGuard::new_with_init(
            tri!(do self.grow_raw(ptr, len, new_len)),
            self,
            len,
            new_len
        );

        for i in 0..to_add {
            guard.init_unchecked((&*src.as_ptr().add(i)).clone());
        }

        Ok(guard.release_first())
    }

    /// Shrinks a slice to a new length, dropping any removed elements.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - `init` must describe exactly the number of initialized elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other`]`("attempted to truncate a slice to a larger size")` if `new_len >
    ///   slice.len()`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn truncate<T>(
        &self,
        slice: NonNull<[T]>,
        init: usize,
        new_len: usize
    ) -> Result<NonNull<[T]>, AllocError> {
        self.truncate_raw(slice.cast::<T>(), nonnull_slice_len(slice), init, new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Shrinks a slice to a new length given the pointer to its first element, current length, and
    /// requested length. This drops any removed elements.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `init` must describe exactly the number of initialized elements in that slice.
    /// - `len` must describe exactly the total number of elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other`]`("attempted to truncate a slice to a larger size")` if `new_len >
    ///   len`.
    #[track_caller]
    unsafe fn truncate_raw<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        init: usize,
        new_len: usize
    ) -> Result<NonNull<T>, AllocError> {
        if new_len > len {
            return Err(AllocError::Other("attempted to truncate a slice to a larger size"));
        }

        if new_len < init {
            let to_drop = init - new_len;
            core::ptr::drop_in_place(crate::helpers::slice_ptr_from_raw_parts(
                ptr.as_ptr().add(new_len),
                to_drop
            ));
        }

        self.shrink_raw(ptr, len, new_len)
    }

    /// Reallocates a slice to a new length, filling any newly allocated bytes with `n`.
    ///
    /// On grow, preserves all existing elements and truncates to `new_len` elements on shrink.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    unsafe fn refsalloc<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        n: u8
    ) -> Result<NonNull<[T]>, AllocError> {
        self.refalloc_raw(slice.cast::<T>(), nonnull_slice_len(slice), new_len, n)
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
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
    unsafe fn refalloc_raw<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        n: u8
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(ralloc, self, ptr, len, new_len, T, Filled(n))
    }

    /// Reallocates a slice to a new length and fills each new element with the result of
    /// `f(elem_idx)`.
    ///
    /// On grow, preserves all existing elements and fills new ones by calling `f(i)`.
    /// On shrink, truncates to `new_len` elements without dropping removed elements.
    ///
    /// # Safety
    ///
    /// `slice` must point to a slice allocated using this allocator.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    #[track_caller]
    unsafe fn resalloc_with<T, F: Fn(usize) -> T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        f: F
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_with(slice.cast::<T>(), nonnull_slice_len(slice), new_len, f)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length, filling any newly allocated elements with the result of `f(elem_idx)`
    /// under a guard to drop and deallocate on panic.
    ///
    /// On grow, preserves all existing elements and fills new ones by calling `f(i)`.
    /// On shrink, truncates to `new_len` elements without dropping removed elements.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    #[track_caller]
    unsafe fn realloc_raw_with<T, F: Fn(usize) -> T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        f: F
    ) -> Result<NonNull<T>, AllocError> {
        match self.realloc_raw(ptr, len, new_len) {
            Ok(p) => {
                if new_len > len {
                    Ok(fill_new_elems_with(&self, p, len, new_len, f))
                } else {
                    Ok(p)
                }
            }
            Err(e) => Err(e)
        }
    }

    /// Reallocates a slice to a new length and clones elements from `src` into any newly allocated
    /// region.
    ///
    /// On grow, preserves existing elements and clones `new_len - slice.len()` elements from `src`
    /// into the new tail.
    /// On shrink, truncates to `new_len` elements without dropping removed elements.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - `src` must contain at least `new_len - slice.len()` readable elements when growing.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other`]`("source slice length is insufficient to fill new elements")` if
    ///   `src_len < new_len - len`.
    #[track_caller]
    unsafe fn resalloc_clone_from<T: Clone>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        src: NonNull<[T]>
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_clone_from(
            slice.cast::<T>(),
            nonnull_slice_len(slice),
            new_len,
            src.cast::<T>(),
            nonnull_slice_len(src)
        )
        .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length, then clones elements from `src` into any newly allocated region.
    ///
    /// On grow, preserves existing elements and clones `new_len - len` elements from `src` into the
    /// new tail.
    /// On shrink, truncates to `new_len` without dropping removed elements.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    /// - `src` must contain at least `new_len - len` readable elements when growing.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other`]`("source slice length is insufficient to fill new elements")` if
    ///   `src_len < new_len - len`.
    #[track_caller]
    unsafe fn realloc_raw_clone_from<T: Clone>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,

        src: NonNull<T>,
        src_len: usize
    ) -> Result<NonNull<T>, AllocError> {
        let new_ptr = tri!(do self.realloc_raw(ptr, len, new_len));

        if new_len > len {
            let to_add = new_len - len;
            if src_len < to_add {
                return Err(INSUF_GROW_SRC);
            }

            let mut guard =
                crate::helpers::SliceAllocGuard::new_with_init(new_ptr, self, len, new_len);

            for i in 0..to_add {
                guard.init_unchecked((&*src.as_ptr().add(i)).clone());
            }

            Ok(guard.release_first())
        } else {
            Ok(new_ptr)
        }
    }

    // TODO: realloc variants which drop removed elements using truncate
    /// Placeholder docs
    #[allow(clippy::missing_errors_doc, clippy::missing_safety_doc)]
    unsafe fn resalloc_truncate<T>(
        &self,
        ptr: NonNull<[T]>,
        init: usize,
        new_len: usize
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_truncate_raw(ptr.cast::<T>(), nonnull_slice_len(ptr), init, new_len)
            .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Placeholder docs
    #[allow(clippy::missing_errors_doc, clippy::missing_safety_doc)]
    unsafe fn realloc_truncate_raw<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        init: usize,
        
        new_len: usize
    ) -> Result<NonNull<T>, AllocError> {
        if len > new_len {
            self.truncate_raw(ptr, len, init, new_len)
        } else { 
            self.grow_raw(ptr, len, new_len)
        }
    }
}

#[cfg(feature = "alloc_ext")]
impl<A: AllocSlice + ?Sized> AllocSliceExt for A {}
