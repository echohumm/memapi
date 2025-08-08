use crate::{
    error::AllocError,
    grow,
    helpers::{
        alloc_then, layout_or_err, nonnull_slice_from_raw_parts, nonnull_slice_len,
        slice_ptr_from_raw_parts, SliceAllocGuard,
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
// TODO: slice growth and realloc with copying and cloning
// TODO: review usage and make small semantic adjustments, like making functions take
//  [MaybeUninit<T>] and an extra `init` count instead of just [T] for ease of use.

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
            Layout::from_size_align_unchecked($len * <$ty>::SZ, <$ty>::ALN),
            layout_or_err::<$ty>($new_len)?,
            $(AllocPattern::<$f>::$pat$(($val))?)?
        )
        .map(NonNull::cast)
    }
}

/// Small helper to fill new elements of a grown slice using a predicate.
#[cfg_attr(miri, track_caller)]
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

/// Small helper to resize and initialize a slice's elements with two predicates.
#[cfg_attr(miri, track_caller)]
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

/// Small helper to allocate a slice using a given allocation function.
#[cfg_attr(miri, track_caller)]
pub(crate) fn alloc_slice<
    T,
    A: Alloc + ?Sized,
    F: Fn(&A, Layout) -> Result<NonNull<u8>, AllocError>,
>(
    a: &A,
    len: usize,
    alloc: F,
) -> Result<NonNull<[T]>, AllocError> {
    alloc(a, layout_or_err::<T>(len)?).map(|ptr| nonnull_slice_from_raw_parts(ptr.cast(), len))
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
    fn alloc_slice<T>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
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
    fn alloc_clone_slice_to<T: Clone>(&self, data: &[T]) -> Result<NonNull<[T]>, AllocError> {
        alloc_then(self, unsafe { data.layout() }, data, |p, data| unsafe {
            let mut guard = SliceAllocGuard::new(p.cast(), self, data.len());
            for elem in data {
                guard.init_unchecked(elem.clone());
            }
            guard.release()
        })
    }

    /// Allocates uninitialized memory for a slice of `T` and copies each element from `data` into
    /// it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if the slice is zero-sized.
    #[cfg_attr(miri, track_caller)]
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
    unsafe fn alloc_copy_slice_to_unchecked<T>(
        &self,
        data: &[T],
    ) -> Result<NonNull<[T]>, AllocError> {
        alloc_then(self, data.layout(), data, |p, data| {
            let p = p.cast::<T>();
            ptr::copy_nonoverlapping((data as *const [T]).cast::<T>(), p.as_ptr(), data.len());

            nonnull_slice_from_raw_parts(p, data.len())
        })
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
    fn alloc_slice_with<T, F: Fn(usize) -> T>(
        &self,
        len: usize,
        f: F,
    ) -> Result<NonNull<[T]>, AllocError> {
        alloc_then(self, layout_or_err::<T>(len)?, f, |p, f| unsafe {
            let mut guard = SliceAllocGuard::new(p.cast(), self, len);
            for i in 0..len {
                guard.init_unchecked(f(i));
            }
            guard.release()
        })
    }

    /// Allocates uninitialized memory for a `[T]` of length `len` and initializes it using `init`.
    ///
    /// `init` receives a pointer to the entire slice and a mutable reference to an initialized
    /// element counter.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    ///
    /// # Safety
    ///
    /// The caller must ensure the initialized element counter will be the same as the slice's
    /// length after `init` finishes, and that at any time `init` may panic, the counter will be
    /// correct.
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_slice_default<T: Default>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
        self.alloc_slice_with(len, |_| T::default())
    }

    // TODO: make these actual bulleted lists instead of just "a, b, c, and d".
    /// Drops `init` elements from a partially initialized slice and deallocates it.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, a valid `[T]` for `init` elements, and a valid `[MaybeUninit<T>]`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn drop_and_dealloc_uninit_slice<T>(&self, ptr: NonNull<[MaybeUninit<T>]>, init: usize) {
        ptr::drop_in_place(slice_ptr_from_raw_parts(ptr.as_ptr().cast::<T>(), init));
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
        ptr::drop_in_place(slice_ptr_from_raw_parts(slice.as_ptr().cast::<T>(), init));
        ptr::write_bytes(slice.as_ptr().cast::<T>(), 0, nonnull_slice_len(slice));
        self.dealloc(slice.cast::<u8>(), slice.layout());
    }

    // TODO: more variants of this, actually use this in places.
    /// Allocates memory for a slice of uninitialized `T` with the given length and returns a
    /// [`SliceAllocGuard`] around it to ensure proper destruction and deallocation on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
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

    /// Extends a slice with elements from a reference to another via either copying or cloning.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    fn extend_slice_from_ref<T: Clone>(
        &self,
        slice: NonNull<[T]>,
        extra: &[T],
    ) -> Result<NonNull<[T]>, AllocError> {
        // SAFETY: a NonNull<[T]> has the exact same layout as a &[T].
        self.extend_slice(slice, unsafe {
            // have to use this superlint instead of just borrow_as_ptr as it doesn't exist in our
            //  msrv
            #[allow(clippy::pedantic)]
            *(&extra as *const &[T]).cast::<NonNull<[T]>>()
        })
    }

    /// Extends a slice with elements from another via either copying or cloning.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    fn extend_slice<T: Clone>(
        &self,
        slice: NonNull<[T]>,
        extra: NonNull<[T]>,
    ) -> Result<NonNull<[T]>, AllocError> {
        let len = nonnull_slice_len(slice);
        let ext_len = nonnull_slice_len(extra);
        self.extend_raw_slice(slice.cast::<T>(), len, extra.cast::<T>(), ext_len)
            .map(|p| nonnull_slice_from_raw_parts(p, len + ext_len))
    }

    /// Extends a slice with elements from another via either copying or cloning, given pointers
    /// to their first elements and their lengths.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    fn extend_raw_slice<T: Clone>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        extra_ptr: NonNull<T>,
        extra_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        trait SpecExtendSlice<T: Clone, A: AllocSlice + ?Sized> {
            fn dupe_into(slf: NonNull<T>, len: usize, dst: NonNull<T>);
        }

        macro_rules! spec_extend_slice_impl {
            ($($extra_token:tt)?) => {
                impl<T: Clone, A: AllocSlice + ?Sized> SpecExtendSlice<T, A> for [T] {
                    $($extra_token)? fn dupe_into(slf: NonNull<T>, len: usize, dst: NonNull<T>) {
                        let p = dst.as_ptr();
                        let slf = slf.as_ptr();

                        unsafe {
                            #[cfg(not(feature = "clone_to_uninit"))]
                            for i in 0..len {
                                p.add(i).write((&*slf.add(i)).clone());
                            }

                            #[cfg(feature = "clone_to_uninit")]
                            <[T] as core::clone::CloneToUninit>::clone_to_uninit(
                                &*slice_ptr_from_raw_parts(slf, len), p.cast()
                            );
                        }
                    }
                }
            };
        }

        #[cfg(not(feature = "specialization"))]
        spec_extend_slice_impl!();

        #[cfg(feature = "specialization")]
        spec_extend_slice_impl!(default);

        #[cfg(feature = "specialization")]
        impl<T: Copy, A: AllocSlice + ?Sized> SpecExtendSlice<T, A> for [T] {
            fn dupe_into(slf: NonNull<T>, len: usize, dst: NonNull<T>) {
                unsafe {
                    ptr::copy(slf.as_ptr(), dst.as_ptr(), len);
                }
            }
        }

        let new_ptr = unsafe { self.grow_raw_slice(ptr, len, len + extra_len)? };
        <[T] as SpecExtendSlice<T, Self>>::dupe_into(extra_ptr, extra_len, new_ptr);
        Ok(new_ptr)
    }

    // TODO: extend_slice_from_iter, alloc_slice_from_iter

    /// Grows a slice to a new length.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be correct.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
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
    /// - at any time `init` may panic, the counter must be correct.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_len > slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_len > len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other("attempted to truncate a slice to a larger size")`] if
    ///   `new_len > slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - `init` must describe exactly the number of initialized elements of that slice.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other("attempted to truncate a slice to a larger size")`] if
    ///   `new_len > len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `init` must describe exactly the number of initialized elements of that slice.
    /// - `len` must describe exactly the total number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
    unsafe fn truncate_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        init: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        if new_len > len {
            return Err(AllocError::Other(
                "attempted to truncate a slice to a larger size",
            ));
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be correct.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be correct.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
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
    unsafe fn dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) {
        // Here, we assume the layout is valid as it was presumably used to allocate previously.
        self.dealloc(
            ptr.cast(),
            Layout::from_size_align_unchecked(T::SZ * n, T::ALN),
        );
    }

    /// Zeroes and deallocates `n` elements at the given pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and a valid `T`.
    #[cfg_attr(miri, track_caller)]
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
    unsafe fn drop_and_dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) {
        ptr::drop_in_place(slice_ptr_from_raw_parts(ptr.as_ptr(), n));
        self.dealloc_n(ptr, n);
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
    fn alloc_slice_filled<T>(&self, len: usize, n: u8) -> Result<NonNull<[T]>, AllocError> {
        alloc_slice(self, len, |a, layout| a.alloc_filled(layout, n))
    }

    /// Attempts to allocate a block of memory for `len` instances of `T` and
    /// fill it by calling `pattern(i)` for each byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    fn alloc_slice_patterned<T, F: Fn(usize) -> u8 + Clone>(
        &self,
        len: usize,
        pattern: F,
    ) -> Result<NonNull<[T]>, AllocError> {
        alloc_slice(self, len, move |a, layout| {
            a.alloc_patterned(layout, pattern.clone())
        })
    }

    /// Grows a slice to a new length, filling any newly allocated bytes with `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
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
            pattern,
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
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
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
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[cfg_attr(miri, track_caller)]
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
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    #[track_caller]
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
            pattern,
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
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    #[track_caller]
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

#[cfg(feature = "alloc_ext")]
impl<A: AllocSlice + ?Sized> AllocSliceExt for A {}
