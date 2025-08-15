use crate::{
    error::{AllocError, ArithOp},
    grow,
    helpers::{
        alloc_then, checked_op, checked_op_panic, layout_or_err, nonnull_slice_from_raw_parts,
        nonnull_slice_len, slice_ptr_from_raw_parts, SliceAllocGuard,
    },
    ralloc, shrink,
    type_props::{PtrProps, SizedProps},
    Alloc, AllocPattern,
};
use alloc::alloc::Layout;
use core::{
    mem::{forget, MaybeUninit},
    ptr::{self, NonNull},
};
// TODO: review usage and make small semantic adjustments, like making functions take
//  [MaybeUninit<T>] and an extra `init` count instead of just [T] for ease of use.
// TODO: check docs like did with alloc_ext

#[cfg(feature = "fallible_dealloc")]
pub use crate::features::fallible_dealloc::slice::DeallocCheckedSlice;

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
        let sz = tri!(AllocError::ArithmeticOverflow(checked_op(<$ty>::SZ, ArithOp::Mul, $len)));
        $fun(
            $self,
            $ptr.cast(),
            tri!(lay, sz, T::ALN),
            tri!(AllocError::InvalidLayout(layout_or_err::<$ty>($new_len))),
            $(AllocPattern::$pat$(($val))?)?
        )
        .map(NonNull::cast)
    }}
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
    let mut guard = SliceAllocGuard::new_with_init(p, a, len, new_len);

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
            let mut guard = SliceAllocGuard::new_with_init(p, a, len, new_len);
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
    fn zalloc_slice<T>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
        alloc_slice(self, len, Self::zalloc)
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
        // SAFETY: `data` is a reference, which immediately fulfills the invariants of layout(); we
        //  just allocated the slice using `self` with space for at least `data.len()`
        //  elements
        unsafe {
            alloc_then(self, data.layout(), data, |p, data| {
                let mut guard = SliceAllocGuard::new(p.cast(), self, data.len());
                for elem in data {
                    guard.init_unchecked(elem.clone());
                }
                guard.release()
            })
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
    fn alloc_copy_slice_to<T: Copy>(&self, data: &[T]) -> Result<NonNull<[T]>, AllocError> {
        // SAFETY: `T: Copy`
        unsafe { self.alloc_copy_slice_to_unchecked(data) }
    }

    /// Allocates uninitialized memory for a slice of `T` and copies each element from `data` into
    /// it.
    ///
    /// This variant doesn't require `T: Copy`.
    ///
    /// # Safety
    ///
    /// Callers must ensure it's safe to copy the elements in `data`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if the slice is zero-sized.
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
        // SAFETY: we just allocated the slice using `self` with space for at least `len` elements
        alloc_then(
            self,
            tri!(AllocError::InvalidLayout(layout_or_err::<T>(len))),
            f,
            |p, f| unsafe {
                let mut guard = SliceAllocGuard::new(p.cast(), self, len);
                for i in 0..len {
                    guard.init_unchecked(f(i));
                }
                guard.release()
            },
        )
    }

    /// Allocates uninitialized memory for a `[T]` of length `len` and initializes it using `init`.
    ///
    /// `init` receives a pointer to the entire slice and a mutable reference to an initialized
    /// element counter.
    ///
    /// If the slice's length is required, use [`nonnull_slice_len`].
    ///
    /// # Safety
    ///
    /// Callers must ensure the initialized element counter will be the same as the slice's length
    /// after `init` finishes, and that at any time `init` may panic, the counter will be correct.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
    #[inline]
    unsafe fn alloc_slice_init<T, I: Fn(NonNull<[T]>, &mut usize)>(
        &self,
        len: usize,
        init: I,
    ) -> Result<NonNull<[T]>, AllocError> {
        let mut guard =
            SliceAllocGuard::new(tri!(do self.alloc_slice::<T>(len)).cast::<T>(), self, len);
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

    /// Drops `init` elements from a partially initialized slice, then zeroes and deallocates its
    /// memory.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - point to a block of memory allocated using this allocator
    /// - be valid for reads, and writes of `n * `[`T::SZ`] bytes
    /// - be properly aligned
    /// - point to `init` valid `T`
    /// - have correct metadata, the total number of `T` which fit in it
    #[track_caller]
    #[inline]
    unsafe fn drop_zero_and_dealloc_uninit_slice<T>(
        &self,
        slice: NonNull<[MaybeUninit<T>]>,
        init: usize,
    ) {
        self.drop_zero_and_dealloc_raw_slice(slice.cast::<T>(), init, nonnull_slice_len(slice));
    }

    /// Drops `init` elements from a pointer to a slice, then zeroes and deallocates its previously
    /// allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must:
    ///   - point to a block of memory allocated using this allocator
    ///   - be valid for reads, and writes of `n * `[`T::SZ`] bytes
    ///   - be properly aligned
    ///   - point to `init` valid `T`
    /// - `len` must be the total number of `T` which fit in that block
    #[track_caller]
    #[inline]
    unsafe fn drop_zero_and_dealloc_raw_slice<T>(
        &self,
        slice: NonNull<T>,
        init: usize,
        len: usize,
    ) {
        ptr::drop_in_place(slice_ptr_from_raw_parts(slice.as_ptr(), init));
        self.zero_and_dealloc_n(slice, len);
    }

    /// Drops `init` elements from a partially initialized slice and deallocates it.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - point to a block of memory allocated using this allocator
    /// - be valid for reads and writes
    /// - be properly aligned
    /// - point to `init` valid `T`
    /// - have correct metadata, the total number of `T` which fit in it
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn drop_and_dealloc_uninit_slice<T>(&self, ptr: NonNull<[MaybeUninit<T>]>, init: usize) {
        self.drop_and_dealloc_raw_slice(ptr.cast::<T>(), init, nonnull_slice_len(ptr));
    }

    /// Drops `init` elements from a pointer to a slice and deallocates its previously allocated
    /// block.
    ///
    /// # Safety
    ///
    /// - `ptr` must:
    ///   - point to a block of memory allocated using this allocator
    ///   - be valid for reads and writes
    ///   - be properly aligned
    ///   - point to `init` valid `T`
    /// - `len` must be the total number of `T` which fit in that block
    #[track_caller]
    #[inline]
    unsafe fn drop_and_dealloc_raw_slice<T>(&self, ptr: NonNull<T>, init: usize, len: usize) {
        ptr::drop_in_place(slice_ptr_from_raw_parts(ptr.as_ptr(), init));
        self.dealloc_n(ptr, len);
    }

    /// Zeroes and deallocates `n` elements at the given pointer.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - point to a block of memory allocated using this allocator
    /// - be valid for writes of `n * `[`T::SZ`] bytes
    /// - be properly aligned
    #[cfg_attr(miri, track_caller)]
    unsafe fn zero_and_dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) {
        ptr::write_bytes(ptr.as_ptr(), 0, n);
        self.dealloc_n(ptr, n);
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
            Layout::from_size_align_unchecked(checked_op_panic(T::SZ, ArithOp::Mul, n), T::ALN),
        );
    }

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
            // SAFETY: we just allocated the slice using `self` with space for at least `len`
            //  elements
            Ok(ptr) => Ok(unsafe { SliceAllocGuard::new(ptr.cast(), self, len) }),
            Err(e) => Err(e),
        }
    }

    /// Extends a slice with elements from a reference to another via either copying or cloning.
    ///
    /// # Safety
    ///
    /// `slice` must point to a slice allocated with this allocator.
    /// `init` must be the number of initialized elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    unsafe fn extend_slice_from_ref<T: Clone>(
        &self,
        slice: NonNull<[T]>,
        init: usize,
        extra: &[T],
    ) -> Result<NonNull<[T]>, AllocError> {
        // SAFETY: a NonNull<[T]> has the exact same layout as a &[T].
        self.extend_slice(slice, init, {
            #[allow(unknown_lints, clippy::borrow_as_ptr)]
            *(&extra as *const &[T]).cast::<NonNull<[T]>>()
        })
    }

    /// Extends a slice with elements from another via either copying or cloning.
    ///
    /// # Safety
    ///
    /// `slice` must point to a slice allocated with this allocator.
    /// `init` must be the number of initialized elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    unsafe fn extend_slice<T: Clone>(
        &self,
        slice: NonNull<[T]>,
        init: usize,
        extra: NonNull<[T]>,
    ) -> Result<NonNull<[T]>, AllocError> {
        let len = nonnull_slice_len(slice);
        let ext_len = nonnull_slice_len(extra);

        self.extend_raw_slice(slice.cast::<T>(), init, len, extra.cast::<T>(), ext_len)
            .map(|p| nonnull_slice_from_raw_parts(p, len + ext_len))
    }

    /// Extends a slice with elements from another via either copying or cloning, given pointers
    /// to their first elements and their lengths.
    ///
    /// # Safety
    ///
    /// `slice` must point to a slice allocated with this allocator.
    /// `init` must be the number of initialized elements in that slice.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[cfg_attr(miri, track_caller)]
    unsafe fn extend_raw_slice<T: Clone>(
        &self,
        ptr: NonNull<T>,
        init: usize,
        len: usize,

        extra_ptr: NonNull<T>,
        extra_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        trait SpecExtendSlice<T: Clone, A: AllocSlice + ?Sized> {
            fn dupe_into(
                a: &A,
                slf: NonNull<T>,
                init: usize,
                len: usize,
                extra_len: usize,
                dst: NonNull<T>,
            );
        }

        macro_rules! spec_extend_slice_impl {
            ($($extra_token:tt)?) => {
                impl<T: Clone, A: AllocSlice + ?Sized> SpecExtendSlice<T, A> for [T] {
                    $($extra_token)? fn dupe_into(
                        a: &A,
                        slf: NonNull<T>,
                        init: usize,
                        len: usize,
                        extra_len: usize,
                        dst: NonNull<T>
                    ) {
                        let slf = slf.as_ptr();

                        // SAFETY: we just allocated the slice using `a` with space for at least
                        //  `len + extra_len` elements, and the caller guarantees that `init` is
                        //  the number of initialized elements in `slf`.
                        unsafe {
                            let mut guard = SliceAllocGuard::new_with_init(
                                dst,
                                a,
                                init,
                                len + extra_len
                            );

                            for i in 0..extra_len {
                                guard.init_unchecked((&*slf.add(i)).clone());
                            }

                            forget(guard);
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
            fn dupe_into(
                _: &A,
                slf: NonNull<T>,
                init: usize,
                _: usize,
                extra_len: usize,
                dst: NonNull<T>,
            ) {
                // SAFETY: we just allocated the slice using `a` with space for at least
                //  'len + extra_len' elements, and the caller guarantees that 'init' is the number
                //  of initialized elements in 'slf'. grow_raw_slice guarantees alignment.
                unsafe {
                    ptr::copy(slf.as_ptr(), dst.as_ptr().add(init), extra_len);
                }
            }
        }

        if extra_len == 0 {
            return Ok(ptr);
        }

        let new_ptr = tri!(do self.grow_raw_slice(ptr, len, len + extra_len));
        <[T] as SpecExtendSlice<T, Self>>::dupe_into(
            self, extra_ptr, init, len, extra_len, new_ptr,
        );
        Ok(new_ptr)
    }

    // TODO: extend_slice_from_iter, alloc_slice_from_iter

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
    unsafe fn grow_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
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
    unsafe fn zgrow_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.zgrow_raw_slice(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
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
    unsafe fn zgrow_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(grow, self, ptr, len, new_len, T, Zeroed)
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
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be correct.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < slice.len()`.
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
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be correct.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_len < len`.
    ///
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
            |a, p, len, new| a.grow_raw_slice(p, len, new),
            init,
        )
    }

    /// Grows a `[T]` to a new length and fills each new element with `T`'s default value.
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
    unsafe fn grow_raw_slice_default<T: Default>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        self.grow_raw_slice_with(ptr, len, new_len, |_| T::default())
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
    unsafe fn grow_slice_clone_from<T: Clone>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        src: NonNull<[T]>,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice_clone_from(
            slice.cast::<T>(),
            nonnull_slice_len(slice),
            new_len,
            src.cast::<T>(),
            nonnull_slice_len(src),
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
    unsafe fn grow_raw_slice_clone_from<T: Clone>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,

        src: NonNull<T>,
        src_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        if new_len == len {
            return Ok(ptr);
        }

        let to_add = new_len - len;
        if src_len < to_add {
            return Err(INSUF_GROW_SRC);
        }

        let mut guard = SliceAllocGuard::new_with_init(
            tri!(do self.grow_raw_slice(ptr, len, new_len)),
            self,
            len,
            new_len,
        );

        for i in 0..to_add {
            guard.init_unchecked((&*src.as_ptr().add(i)).clone());
        }

        Ok(guard.release_first())
    }

    /// Grows a slice to a new length and copies elements from `src` into the newly allocated
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
    unsafe fn grow_slice_copy_from<T: Copy>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        src: NonNull<[T]>,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_slice_copy_from_unchecked(slice, new_len, src)
    }

    /// Grows a slice to a new length and copies elements from `src` into the newly allocated
    /// region.
    ///
    /// This variant doesn't require `T: Copy`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - `src` must contain at least `new_len - slice.len()` readable, safe-to-copy elements.
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
    unsafe fn grow_slice_copy_from_unchecked<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        src: NonNull<[T]>,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice_copy_from_unchecked(
            slice.cast::<T>(),
            nonnull_slice_len(slice),
            new_len,
            src.cast::<T>(),
            nonnull_slice_len(src),
        )
        .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length, then copies elements from `src` into the newly allocated region.
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
    unsafe fn grow_raw_slice_copy_from<T: Copy>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,

        src: NonNull<T>,
        src_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        self.grow_raw_slice_copy_from_unchecked(ptr, len, new_len, src, src_len)
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length, then copies elements from `src` into the newly allocated region.
    ///
    /// This variant doesn't require `T: Copy`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    /// - `src` must contain at least `new_len - len` readable, safe-to-copy elements.
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
    unsafe fn grow_raw_slice_copy_from_unchecked<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,

        src: NonNull<T>,
        src_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        if new_len == len {
            return Ok(ptr);
        }

        let to_add = new_len - len;
        if src_len < to_add {
            return Err(INSUF_GROW_SRC);
        }

        let new_ptr = tri!(do self.grow_raw_slice(ptr, len, new_len));
        ptr::copy_nonoverlapping(src.as_ptr(), new_ptr.as_ptr().add(len), to_add);
        Ok(new_ptr)
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
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_len > slice.len()`.
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
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_len > len`.
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
    /// - [`AllocError::Other`]`("attempted to truncate a slice to a larger size")` if
    ///   `new_len > slice.len()`.
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
    /// - [`AllocError::Other`]`("attempted to truncate a slice to a larger size")` if
    ///   `new_len > len`.
    #[track_caller]
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
    unsafe fn realloc_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
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
    unsafe fn rezalloc_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.rezalloc_raw_slice(slice.cast::<T>(), nonnull_slice_len(slice), new_len)
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
    unsafe fn rezalloc_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(ralloc, self, ptr, len, new_len, T, Zeroed)
    }

    // TODO: doc ordering below here

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
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be correct.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
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
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    /// - the initialized element counter must be the same as the slice's length after `init`
    ///   finishes
    /// - at any time `init` may panic, the counter must be correct.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
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
            |a, p, len, new| a.realloc_raw_slice(p, len, new),
            init,
        )
    }

    /// Reallocates a slice to a new length and fills each new element with `T`'s default value.
    ///
    /// On grow, preserves all existing elements and fills new ones by calling `T::default()`.
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
    #[track_caller]
    unsafe fn realloc_raw_slice_default<T: Default>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        self.realloc_raw_slice_with(ptr, len, new_len, |_| T::default())
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
    unsafe fn realloc_slice_clone_from<T: Clone>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        src: NonNull<[T]>,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_slice_clone_from(
            slice.cast::<T>(),
            nonnull_slice_len(slice),
            new_len,
            src.cast::<T>(),
            nonnull_slice_len(src),
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
    unsafe fn realloc_raw_slice_clone_from<T: Clone>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,

        src: NonNull<T>,
        src_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        let new_ptr = tri!(do self.realloc_raw_slice(ptr, len, new_len));

        if new_len > len {
            let to_add = new_len - len;
            if src_len < to_add {
                return Err(INSUF_GROW_SRC);
            }

            let mut guard = SliceAllocGuard::new_with_init(new_ptr, self, len, new_len);

            for i in 0..to_add {
                guard.init_unchecked((&*src.as_ptr().add(i)).clone());
            }

            Ok(guard.release_first())
        } else {
            Ok(new_ptr)
        }
    }

    /// Reallocates a slice to a new length and copies elements from `src` into any newly allocated
    /// region.
    ///
    /// On grow, preserves existing elements and copies `new_len - slice.len()` elements from `src`
    /// into the new tail. On shrink, truncates to `new_len` elements without dropping removed
    /// elements.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - `src` must contain at least `new_len - slice.len()` readable elements when growing.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other`]`("source slice length is insufficient to fill new elements")` if
    ///   `src_len < new_len - len`.
    #[track_caller]
    unsafe fn realloc_slice_copy_from<T: Copy>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        src: NonNull<[T]>,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_slice_copy_from_unchecked(slice, new_len, src)
    }

    /// Reallocates a slice to a new length and copies elements from `src` into any newly allocated
    /// region.
    ///
    /// On grow, preserves existing elements and copies `new_len - slice.len()` elements from `src`
    /// into the new tail. On shrink, truncates to `new_len` elements without dropping removed
    /// elements.
    ///
    /// This variant doesn't require `T: Copy`.
    ///
    /// # Safety
    ///
    /// - `slice` must point to a slice allocated using this allocator.
    /// - `src` must contain at least `new_len - slice.len()` readable, safe-to-copy elements when
    ///   growing.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other`]`("source slice length is insufficient to fill new elements")` if
    ///   `src_len < new_len - len`.
    #[track_caller]
    unsafe fn realloc_slice_copy_from_unchecked<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        src: NonNull<[T]>,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.realloc_raw_slice_copy_from_unchecked(
            slice.cast::<T>(),
            nonnull_slice_len(slice),
            new_len,
            src.cast::<T>(),
            nonnull_slice_len(src),
        )
        .map(|p| nonnull_slice_from_raw_parts(p, new_len))
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length, then copies elements from `src` into any newly allocated region.
    ///
    /// On grow, preserves existing elements and copies `new_len - len` elements from `src`
    /// into the new tail. On shrink, truncates to `new_len` without dropping removed elements.
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
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other`]`("source slice length is insufficient to fill new elements")` if
    ///   `src_len < new_len - len`.
    #[track_caller]
    unsafe fn realloc_raw_slice_copy_from<T: Copy>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,

        src: NonNull<T>,
        src_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        self.realloc_raw_slice_copy_from_unchecked(ptr, len, new_len, src, src_len)
    }

    /// Reallocates a slice to a new length given the pointer to its first element, current length,
    /// and requested length, then copies elements from `src` into any newly allocated region.
    ///
    /// On grow, preserves existing elements and copies `new_len - len` elements from `src`
    /// into the new tail. On shrink, truncates to `new_len` without dropping removed elements.
    ///
    /// This variant doesn't require `T: Copy`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of elements in that slice.
    /// - `src` must contain at least `new_len - len` readable, safe-to-copy elements when growing.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::InvalidLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice would be zero-sized.
    /// - [`AllocError::Other`]`("source slice length is insufficient to fill new elements")` if
    ///   `src_len < new_len - len`.
    #[track_caller]
    unsafe fn realloc_raw_slice_copy_from_unchecked<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,

        src: NonNull<T>,
        src_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        let new_ptr = tri!(do self.realloc_raw_slice(ptr, len, new_len));

        if new_len > len {
            let to_add = new_len - len;
            if src_len != to_add {
                return Err(INSUF_GROW_SRC);
            }

            ptr::copy_nonoverlapping(src.as_ptr(), new_ptr.as_ptr().add(len), to_add);
        }

        Ok(new_ptr)
    }

    // TODO: realloc variants which drop removed elements using truncate
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
    fn falloc_slice<T>(&self, len: usize, n: u8) -> Result<NonNull<[T]>, AllocError> {
        alloc_slice(self, len, |a, layout| a.falloc(layout, n))
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
    unsafe fn fgrow_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        n: u8,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.fgrow_raw_slice(slice.cast::<T>(), nonnull_slice_len(slice), new_len, n)
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
    unsafe fn fgrow_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        n: u8,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(grow, self, ptr, len, new_len, T, Filled(n))
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
    unsafe fn refalloc_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
        n: u8,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.refalloc_raw_slice(slice.cast::<T>(), nonnull_slice_len(slice), new_len, n)
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
    unsafe fn refalloc_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
        n: u8,
    ) -> Result<NonNull<T>, AllocError> {
        realloc!(ralloc, self, ptr, len, new_len, T, Filled(n))
    }
}

#[cfg(feature = "alloc_ext")]
impl<A: AllocSlice + ?Sized> AllocSliceExt for A {}
