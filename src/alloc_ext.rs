#[cfg(feature = "metadata")]
use crate::UnsizedCopy;
use crate::{
    Alloc, AllocError, PtrProps, SizedProps,
    helpers::{AllocGuard, SliceAllocGuard},
    layout_or_sz_align,
};
#[cfg(feature = "clone_to_uninit")]
use core::clone::CloneToUninit;
#[cfg(feature = "metadata")]
use core::ptr::metadata;
use core::{alloc::Layout, ptr::NonNull};

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
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    #[track_caller]
    #[inline]
    unsafe fn grow_slice<T>(
        &self,
        ptr: NonNull<[T]>,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        self.grow_raw_slice(ptr.cast(), ptr.len(), new_len)
    }

    /// Grows a slice to a new length given the pointer to its first element, current length, and
    /// requested length.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slice allocated using this allocator.
    /// - `len` must describe exactly the number of initialized elements in that slice.
    #[track_caller]
    #[inline]
    unsafe fn grow_raw_slice<T>(
        &self,
        ptr: NonNull<T>,
        len: usize,
        new_len: usize,
    ) -> Result<NonNull<[T]>, AllocError> {
        unsafe {
            self.grow(
                ptr.cast(),
                layout_or_sz_align::<T>(len)
                    .map_err(|(sz, aln)| AllocError::LayoutError(sz, aln))?,
                layout_or_sz_align::<T>(new_len)
                    .map_err(|(sz, aln)| AllocError::LayoutError(sz, aln))?,
            )
            .map(|ptr| NonNull::slice_from_raw_parts(ptr.cast(), new_len))
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

    /// Deallocates a previously cloned or written slice of `T`.
    ///
    /// # Safety
    ///
    /// - `slice_ptr` must point to a block of memory allocated using this allocator.
    #[track_caller]
    #[inline]
    unsafe fn dealloc_slice<T>(&self, slice_ptr: NonNull<[T]>) {
        self.dealloc_typed(slice_ptr);
    }

    /// Drops and deallocates a previously cloned or written slice of `T`.
    ///
    /// # Safety
    ///
    /// - `slice_ptr` must point to a block of memory allocated using this allocator, be valid for
    ///   reads and writes, aligned, and a valid `T`.
    #[track_caller]
    #[inline]
    unsafe fn drop_and_dealloc_slice<T>(&self, slice_ptr: NonNull<[T]>) {
        slice_ptr.drop_in_place();
        self.dealloc_slice(slice_ptr);
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

    #[cfg(feature = "metadata")]
    /// Allocates and copies an unsized `T` by reference, returning a `NonNull<T>`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
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
    #[track_caller]
    #[inline]
    unsafe fn alloc_copy_ref_to_unchecked<T: ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        match self.alloc(Layout::for_value(data)) {
            Ok(ptr) => Ok({
                ptr.copy_from_nonoverlapping(
                    NonNull::from_ref(data).cast(),
                    size_of_val::<T>(data),
                );
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
    #[track_caller]
    #[inline]
    unsafe fn alloc_copy_ptr_to_unchecked<T: ?Sized + UnsizedCopy>(
        &self,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        match self.alloc(Layout::for_value(&*data)) {
            Ok(ptr) => Ok({
                ptr.copy_from_nonoverlapping(*data.cast(), size_of_val::<T>(&*data));
                NonNull::from_raw_parts(ptr, metadata(data))
            }),
            Err(e) => Err(e),
        }
    }
}

impl<A: Alloc> AllocExt for A {}
