#[cfg(feature = "metadata")]
use crate::UnsizedCopy;
use crate::{
    helpers::{AllocGuard, SliceAllocGuard},
    layout_or_sz_align, Alloc, AllocError, PtrProps, SizedProps,
};
#[cfg(feature = "clone_to_uninit")]
use core::clone::CloneToUninit;
#[cfg(feature = "metadata")]
use core::ptr::metadata;
use core::{alloc::Layout, mem::MaybeUninit, ptr::NonNull};

// TODO: slice growth with zeroing, filling, patterning, initializing, etc., slice shrinking with 
//  init elem dropping

/// Extension methods for the core [`Alloc`] trait, providing convenient
/// routines to allocate, initialize, clone, copy, and deallocate sized
/// and unsized types.
///
/// These helpers simplify common allocation patterns by combining
/// `alloc`, writes, drops, and deallocations for various data shapes.
pub trait AllocExt: Alloc {
    /// Allocates uninitialized memory for a single `T` and initializes it using `init`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[track_caller]
    #[inline]
    fn alloc_init<T, I: Fn(NonNull<T>)>(&self, init: I) -> Result<NonNull<T>, AllocError> {
        let guard = AllocGuard::new(self.alloc(T::LAYOUT)?.cast::<T>(), self);
        init(*guard);
        Ok(guard.release())
    }

    /// Allocates uninitialized memory for a `[T]` of length `len` and initializes it using `init`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    fn alloc_init_slice<T, I: Fn(NonNull<[T]>)>(
        &self,
        init: I,
        len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        let guard = AllocGuard::new(self.alloc_slice(len)?, self);
        init(*guard);
        Ok(guard.release())
    }

    /// Allocates uninitialized memory for a single `T` and writes `T`'s default into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[track_caller]
    #[inline]
    fn alloc_default<T: Default>(&self) -> Result<NonNull<T>, AllocError> {
        self.alloc_write(T::default())
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
    fn alloc_default_slice<T: Default>(&self, len: usize) -> Result<NonNull<[T]>, AllocError> {
        self.alloc_slice_with(len, |_| T::default())
    }

    /// Allocates uninitialized memory for a single `T` and writes `data` into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[track_caller]
    #[inline]
    fn alloc_write<T>(&self, data: T) -> Result<NonNull<T>, AllocError> {
        match self.alloc(Layout::new::<T>()) {
            Ok(ptr) => Ok(unsafe {
                let ptr = ptr.cast();
                ptr.write(data);
                ptr
            }),
            Err(e) => Err(e),
        }
    }

    #[cfg(not(feature = "clone_to_uninit"))]
    /// Allocates uninitialized memory for a single `T` and clones `data` into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[track_caller]
    #[inline]
    fn alloc_clone_to<T: Clone>(&self, data: &T) -> Result<NonNull<T>, AllocError> {
        match self.alloc(Layout::new::<T>()) {
            Ok(ptr) => Ok(unsafe {
                let guard = AllocGuard::new(ptr.cast(), self);
                guard.write(data.clone());
                guard.release()
            }),
            Err(e) => Err(e),
        }
    }

    #[cfg(all(feature = "clone_to_uninit", feature = "metadata"))]
    /// Allocates uninitialized memory for a single `T` and clones `data` into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[track_caller]
    #[inline]
    fn alloc_clone_to<T: CloneToUninit + ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        match self.alloc(Layout::for_value::<T>(data)) {
            Ok(ptr) => Ok(unsafe {
                let guard =
                    AllocGuard::new(NonNull::<T>::from_raw_parts(ptr, metadata(data)), self);
                data.clone_to_uninit(guard.as_ptr().cast());
                guard.release()
            }),
            Err(e) => Err(e),
        }
    }

    #[cfg(all(feature = "clone_to_uninit", not(feature = "metadata")))]
    /// Allocates uninitialized memory for a single `T` and clones `data` into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[track_caller]
    #[inline]
    fn alloc_clone_to<T: CloneToUninit>(&self, data: &T) -> Result<NonNull<T>, AllocError> {
        match self.alloc(Layout::for_value::<T>(data)) {
            Ok(ptr) => Ok(unsafe {
                let guard = AllocGuard::new(ptr, self);
                data.clone_to_uninit(guard.as_ptr());
                guard.release().cast()
            }),
            Err(e) => Err(e),
        }
    }

    /// Allocates uninitialized memory for a slice of `T` and clones each element.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if the slice is zero-sized.
    #[track_caller]
    #[inline]
    fn alloc_clone_slice_to<T: Clone>(&self, data: &[T]) -> Result<NonNull<[T]>, AllocError> {
        match self.alloc(Layout::for_value(data)) {
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

    /// Allocates uninitialized memory for a `[T]` of length `len` and fills each element
    /// with the result of `f(elem_idx)`.
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
    #[track_caller]
    #[inline]
    unsafe fn grow_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice(slice.cast::<T>(), slice.len(), new_len)
            .map(|p| NonNull::slice_from_raw_parts(p, new_len))
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length.
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
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of initialized elements in that slice.
    // Safety #2 implies that `len` must be a valid length for the slice (which is required because
    // we use from_size_align_unchecked)
    #[track_caller]
    #[inline]
    unsafe fn grow_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        unsafe {
            self.grow(
                ptr.cast(),
                Layout::from_size_align_unchecked(len * T::SZ, T::ALIGN),
                layout_or_sz_align::<T>(new_len)
                    .map_err(|(sz, aln)| AllocError::LayoutError(sz, aln))?,
            )
            .map(NonNull::cast)
        }
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
    unsafe fn shrink_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.shrink_raw_slice(slice.cast::<T>(), slice.len(), new_len)
            .map(|p| NonNull::slice_from_raw_parts(p, new_len))
    }

    /// Shrinks a slice to a new length given the pointer to its first element, current length, and
    /// requested length. This does not drop any removed elements.
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
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of initialized elements in that slice.
    unsafe fn shrink_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        unsafe {
            self.shrink(
                ptr.cast(),
                Layout::from_size_align_unchecked(len * T::SZ, T::ALIGN),
                layout_or_sz_align::<T>(new_len)
                    .map_err(|(sz, aln)| AllocError::LayoutError(sz, aln))?,
            )
            .map(NonNull::cast)
        }
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
    unsafe fn realloc_slice<T>(
        &self,
        slice: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        self.realloc_raw_slice(slice.cast::<T>(), slice.len(), new_len)
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
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_len > slice.len()`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of initialized elements in that slice.
    unsafe fn realloc_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<T>, AllocError> {
        unsafe {
            self.realloc(
                ptr.cast(),
                Layout::from_size_align_unchecked(len * T::SZ, T::ALIGN),
                layout_or_sz_align::<T>(new_len)
                    .map_err(|(sz, aln)| AllocError::LayoutError(sz, aln))?,
            )
            .map(NonNull::cast)
        }
    }

    /// Zeroes and deallocates the memory at a pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `layout` must describe exactly the same block.
    #[track_caller]
    #[inline]
    unsafe fn zero_and_dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        ptr.as_ptr().write_bytes(0, layout.size());
        self.dealloc(ptr, layout);
    }

    /// Deallocates a pointer's memory.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    #[track_caller]
    #[inline]
    unsafe fn dealloc_typed<T: ?Sized>(&self, ptr: NonNull<T>) {
        self.dealloc(ptr.cast::<u8>(), Layout::for_value(&*ptr.as_ptr()));
    }

    /// Zeroes and deallocates the memory at a pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    #[track_caller]
    #[inline]
    unsafe fn zero_and_dealloc_typed<T: ?Sized>(&self, ptr: NonNull<T>) {
        ptr.cast::<u8>().write_bytes(0, ptr.size());
        self.dealloc_typed(ptr);
    }

    /// Drops the value at the given pointer, then zeroes and deallocates its memory.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and a valid `T`.
    #[track_caller]
    #[inline]
    unsafe fn drop_zero_and_dealloc<T: ?Sized>(&self, ptr: NonNull<T>) {
        ptr.drop_in_place();
        self.zero_and_dealloc_typed(ptr);
    }

    /// Zeroes and deallocates `n` elements at the given pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and a valid `T`.
    #[track_caller]
    #[inline]
    unsafe fn zero_and_dealloc_n<T>(&self, ptr: NonNull<T>, n: usize) {
        ptr.as_ptr().write_bytes(0, n);
        self.dealloc_n(ptr, n);
    }

    /// Drops `init` elements from a partially initialized slice and deallocates it.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, a valid `[T]` for `init` elements, and a valid `[MaybeUninit<T>]`.
    #[track_caller]
    #[inline]
    unsafe fn drop_and_dealloc_uninit_slice<T>(&self, ptr: NonNull<[MaybeUninit<T>]>, init: usize) {
        NonNull::slice_from_raw_parts(ptr.cast::<T>(), init).drop_in_place();
        self.dealloc_typed(ptr);
    }

    /// Drops `init` elements from a partially initialized slice, then zeroes and deallocates its
    /// memory.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and a valid `T`.
    #[track_caller]
    #[inline]
    unsafe fn drop_zero_and_dealloc_uninit_slice<T>(
        &self,
        ptr: NonNull<[MaybeUninit<T>]>,
        init: usize,
    ) {
        NonNull::slice_from_raw_parts(ptr.cast::<T>(), init).drop_in_place();
        ptr.cast::<T>().write_bytes(0, ptr.len());
        self.dealloc_typed(ptr);
    }

    #[cfg(feature = "metadata")]
    /// Allocates and copies an unsized `T` by reference, returning a `NonNull<T>`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[track_caller]
    #[inline]
    fn alloc_copy_ref_to<T: ?Sized + UnsizedCopy>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        unsafe { self.alloc_copy_ref_to_unchecked(data) }
    }

    #[cfg(feature = "metadata")]
    /// Allocates and copies an unsized `T` by raw pointer, returning a `NonNull<T>`.
    ///
    /// # Safety
    ///
    /// - The caller must ensure `data` is a valid pointer to copy from.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[track_caller]
    #[inline]
    unsafe fn alloc_copy_ptr_to<T: ?Sized + UnsizedCopy>(
        &self,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        unsafe { self.alloc_copy_ptr_to_unchecked(data) }
    }

    #[cfg(feature = "metadata")]
    /// Allocates and copies an unsized `T` by reference without requiring
    /// `T: `[`UnsizedCopy`](UnsizedCopy), returning a `NonNull<T>`.
    ///
    /// # Safety
    ///
    /// - The caller must ensure `data` is safe to copy.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[track_caller]
    #[inline]
    unsafe fn alloc_copy_ref_to_unchecked<T: ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        match self.alloc(Layout::for_value(data)) {
            Ok(ptr) => Ok({
                NonNull::from_ref(data)
                    .cast()
                    .copy_to_nonoverlapping(ptr, size_of_val::<T>(data));
                NonNull::from_raw_parts(ptr, metadata(&raw const *data))
            }),
            Err(e) => Err(e),
        }
    }

    #[cfg(feature = "metadata")]
    /// Allocates and copies an unsized `T` by raw pointer without requiring
    /// `T: `[`UnsizedCopy`](UnsizedCopy), returning a `NonNull<T>`.
    ///
    /// # Safety
    ///
    /// - The caller must ensure `data` is safe to copy.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[track_caller]
    #[inline]
    unsafe fn alloc_copy_ptr_to_unchecked<T: ?Sized>(
        &self,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        match self.alloc(Layout::for_value(&*data)) {
            Ok(ptr) => Ok({
                NonNull::new_unchecked(data.cast_mut().cast())
                    .copy_to_nonoverlapping(ptr, size_of_val::<T>(&*data));
                NonNull::from_raw_parts(ptr, metadata(data))
            }),
            Err(e) => Err(e),
        }
    }

    /// Allocates memory for an uninitialized `T` and returns an [`AllocGuard`] around it to ensure
    /// deallocation on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[track_caller]
    #[inline]
    fn alloc_guard<T>(&'_ self) -> Result<AllocGuard<'_, T, Self>, AllocError> {
        match self.alloc(T::LAYOUT) {
            Ok(ptr) => Ok(AllocGuard::new(ptr.cast(), self)),
            Err(e) => Err(e),
        }
    }

    /// Allocates memory for a slice of uninitialized `T` with the given length and returns a
    /// [`SliceAllocGuard`] around it to ensure proper destruction and deallocation on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    /// - [`AllocError::ZeroSizedLayout`] if the computed slice has a size of zero.
    #[track_caller]
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
}

impl<A: Alloc> AllocExt for A {}
