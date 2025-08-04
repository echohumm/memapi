use crate::{
    error::AllocError,
    grow,
    helpers::{alloc_write, AllocGuard},
    ralloc,
    type_props::{PtrProps, SizedProps},
    Alloc, AllocPattern,
};
use core::{alloc::Layout, ptr::{self, NonNull}};

/// Extension methods for the core [`Alloc`] trait, providing convenient routines to allocate,
/// initialize, clone, copy, and deallocate sized and unsized types.
///
/// These helpers simplify common allocation patterns by combining `alloc`, writes, drops, and
/// deallocations for various data shapes.
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

    /// Allocates uninitialized memory for a single `T` and writes `T`'s default into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[track_caller]
    #[inline]
    fn alloc_default<T: Default>(&self) -> Result<NonNull<T>, AllocError> {
        alloc_write(self, T::default())
    }

    /// Allocates uninitialized memory for a single `T` and writes `data` into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_write<T>(&self, data: T) -> Result<NonNull<T>, AllocError> {
        alloc_write(self, data)
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
        match self.alloc(T::LAYOUT) {
            Ok(ptr) => Ok({
                let guard = AllocGuard::new(ptr.cast(), self);
                guard.init(data.clone());
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
    fn alloc_clone_to<T: core::clone::CloneToUninit + ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        match self.alloc(unsafe { data.layout() }) {
            Ok(ptr) => Ok(unsafe {
                let guard = AllocGuard::new(
                    NonNull::<T>::from_raw_parts(ptr, ptr::metadata(data)),
                    self,
                );
                data.clone_to_uninit(guard.as_ptr() as *mut u8);
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
    ///
    /// # Safety
    ///
    // we can't drop the value on panic because we don't have the metadata feature to construct the
    // fat pointer which the guard would use to drop it.
    /// The caller must ensure the cloning operation will never panic or that it is safe to skip
    /// dropping the cloned value.
    #[track_caller]
    #[inline]
    unsafe fn alloc_clone_to<T: core::clone::CloneToUninit + ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<u8>, AllocError> {
        match self.alloc(unsafe { data.layout() }) {
            Ok(ptr) => Ok(unsafe {
                let guard = AllocGuard::new(ptr, self);
                data.clone_to_uninit(guard.as_ptr());
                guard.release()
            }),
            Err(e) => Err(e),
        }
    }

    /// Attempts to allocate a block of memory fitting the given [`Layout`], filled with bytes
    /// initialized to `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError> {
        match self.alloc(layout) {
            Ok(p) => {
                unsafe {
                    ptr::write_bytes(p.as_ptr(), n, layout.size());
                }
                Ok(p)
            }
            Err(e) => Err(e),
        }
    }

    /// Attempts to allocate a block of memory fitting the given [`Layout`] and
    /// fill it by calling `pattern(i)` for each byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    #[track_caller]
    #[inline]
    fn alloc_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError> {
        match self.alloc(layout) {
            Ok(p) => {
                let guard = AllocGuard::new(p.cast::<u8>(), self);
                for i in 0..layout.size() {
                    unsafe {
                        ptr::write(guard.as_ptr().add(i), pattern(i));
                    }
                }
                Ok(guard.release())
            }
            Err(e) => Err(e),
        }
    }

    /// Drops the data at a pointer and deallocates its previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and a valid `T`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn drop_and_dealloc<T: ?Sized>(&self, ptr: NonNull<T>) {
        ptr::drop_in_place(ptr.as_ptr());
        self.dealloc(ptr.cast::<u8>(), ptr.layout());
    }

    /// Zeroes and deallocates the memory at a pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `layout` must describe exactly the same block.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zero_and_dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        ptr::write_bytes(ptr.as_ptr(), 0, layout.size());
        self.dealloc(ptr, layout);
    }

    /// Deallocates a pointer's memory.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc_typed<T: ?Sized>(&self, ptr: NonNull<T>) {
        self.dealloc(ptr.cast::<u8>(), ptr.layout());
    }

    /// Zeroes and deallocates the memory at a pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zero_and_dealloc_typed<T: ?Sized>(&self, ptr: NonNull<T>) {
        ptr::write_bytes(ptr.as_ptr() as *mut u8, 0, ptr.size());
        self.dealloc_typed(ptr);
    }

    /// Drops the value at the given pointer, then zeroes and deallocates its memory.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and a valid `T`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn drop_zero_and_dealloc<T: ?Sized>(&self, ptr: NonNull<T>) {
        ptr::drop_in_place(ptr.as_ptr());
        self.zero_and_dealloc_typed(ptr);
    }

    #[cfg(feature = "metadata")]
    /// Allocates and copies an unsized `T` by reference, returning a `NonNull<T>`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_copy_ref_to<T: ?Sized + crate::marker::UnsizedCopy>(
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
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_copy_ptr_to<T: ?Sized + crate::marker::UnsizedCopy>(
        &self,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        unsafe { self.alloc_copy_ptr_to_unchecked(data) }
    }

    #[cfg(feature = "metadata")]
    /// Allocates and copies an unsized `T` by reference without requiring
    /// `T: `[`UnsizedCopy`](crate::marker::UnsizedCopy), returning a `NonNull<T>`.
    ///
    /// # Safety
    ///
    /// - The caller must ensure `data` is safe to copy.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_copy_ref_to_unchecked<T: ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        match self.alloc(data.layout()) {
            Ok(ptr) => Ok({
                ptr::copy_nonoverlapping(
                    data as *const T as *const u8,
                    ptr.as_ptr(),
                    data.size(),
                );
                NonNull::from_raw_parts(ptr, ptr::metadata(data as *const T))
            }),
            Err(e) => Err(e),
        }
    }

    #[cfg(feature = "metadata")]
    /// Allocates and copies an unsized `T` by raw pointer without requiring
    /// `T: `[`UnsizedCopy`](crate::marker::UnsizedCopy), returning a `NonNull<T>`.
    ///
    /// # Safety
    ///
    /// - The caller must ensure `data` is safe to copy.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_copy_ptr_to_unchecked<T: ?Sized>(
        &self,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        crate::helpers::alloc_copy_ptr_to_unchecked(self, data)
    }

    /// Allocates memory for an uninitialized `T` and returns an [`AllocGuard`] around it to ensure
    /// deallocation on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_guard<T>(&'_ self) -> Result<AllocGuard<'_, T, Self>, AllocError> {
        match self.alloc(T::LAYOUT) {
            Ok(ptr) => Ok(AllocGuard::new(ptr.cast(), self)),
            Err(e) => Err(e),
        }
    }

    /// Grow the given block to a new, larger layout, filling any newly allocated bytes by calling
    /// `pattern(i)` for each new byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
    unsafe fn grow_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError> {
        grow(self, ptr, old_layout, new_layout, AllocPattern::Fn(pattern))
    }

    /// Grows the given block to a new, larger layout, filling any newly allocated bytes with `n`.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<NonNull<u8>, AllocError> {
        grow(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::All(n),
        )
    }

    /// Reallocate a block, growing or shrinking as needed, filling any new bytes by calling
    /// `pattern(i)` for each new byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
    unsafe fn realloc_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError> {
        ralloc(self, ptr, old_layout, new_layout, AllocPattern::Fn(pattern))
    }

    /// Reallocate a block, growing or shrinking as needed, filling any newly
    /// allocated bytes with `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<NonNull<u8>, AllocError> {
        ralloc(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::All(n),
        )
    }
}

impl<A: Alloc + ?Sized> AllocExt for A {}
