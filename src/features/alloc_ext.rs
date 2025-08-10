use crate::helpers::SliceAllocGuard;
use crate::{
    error::AllocError,
    grow,
    helpers::{alloc_then, AllocGuard},
    ralloc,
    type_props::{PtrProps, SizedProps},
    Alloc, AllocPattern,
};
use core::{
    alloc::Layout,
    ptr::{self, NonNull},
};

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
        let guard = tri!(self.alloc_guard());
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

    /// Allocates uninitialized memory for a single `T` and writes `data` into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc_write<T>(&self, data: T) -> Result<NonNull<T>, AllocError> {
        alloc_then::<NonNull<T>, Self, T, _>(self, T::LAYOUT, data, |p, data| unsafe {
            let ptr: NonNull<T> = p.cast();
            ptr::write(ptr.as_ptr(), data);
            ptr
        })
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
        let mut guard = tri!(self.alloc_guard());
        guard.init(data.clone());
        Ok(guard.release())
    }

    #[cfg(all(feature = "clone_to_uninit", feature = "metadata"))]
    /// Allocates uninitialized memory for a single `T` and clones `data` into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[track_caller]
    fn alloc_clone_to<T: core::clone::CloneToUninit + ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        alloc_then(self, unsafe { data.layout() }, data, |p, data| unsafe {
            let guard = AllocGuard::new(
                NonNull::new_unchecked(crate::unstable_util::with_meta(p.as_ptr(), data)),
                self,
            );
            data.clone_to_uninit(guard.as_ptr().cast::<u8>());
            guard.release()
        })
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
    /// Callers must ensure that if the cloning operation panics, it will not be necessary to drop
    /// the clone.
    ///
    /// This is because the `metadata` feature is not enabled, which is required to drop this
    /// unsized value.
    #[track_caller]
    unsafe fn alloc_clone_to<T: core::clone::CloneToUninit + ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<u8>, AllocError> {
        alloc_then::<NonNull<u8>, Self, &T, _>(self, data.layout(), data, |p, data| {
            let guard = crate::helpers::SliceAllocGuard::new(p, self, data.size());
            data.clone_to_uninit(guard.as_ptr());
            guard.release_first()
        })
    }

    /// Attempts to allocate a block of memory fitting the given [`Layout`], filled with bytes
    /// initialized to `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    #[cfg_attr(miri, track_caller)]
    fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError> {
        alloc_then::<NonNull<u8>, Self, u8, _>(self, layout, n, |p, n| {
            unsafe {
                ptr::write_bytes(p.as_ptr(), n, layout.size());
            }
            p
        })
    }

    /// Attempts to allocate a block of memory fitting the given [`Layout`] and
    /// fill it by calling `pattern(i)` for each byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    #[track_caller]
    fn alloc_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        layout: Layout,
        pat: F,
    ) -> Result<NonNull<u8>, AllocError> {
        alloc_then::<NonNull<u8>, Self, F, _>(self, layout, pat, |p, pat| {
            // SAFETY: we just allocated the memory using `self` with space for at least
            //  `layout.size()` bytes
            let mut guard = unsafe { SliceAllocGuard::new(p, self, layout.size()) };
            for i in 0..layout.size() {
                unsafe {
                    guard.init_unchecked(pat(i));
                }
            }
            guard.release_first()
        })
    }

    /// Drops the data at a pointer and deallocates its previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator, be valid for reads
    ///   and writes, aligned, and a valid `T`.
    #[track_caller]
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
        ptr::write_bytes(ptr.as_ptr().cast::<u8>(), 0, ptr.size());
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
    /// - Callers must ensure `data` is a valid pointer to copy from.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[cfg_attr(miri, track_caller)]
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
    /// - Callers must ensure `data` is safe to copy.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_copy_ref_to_unchecked<T: ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        self.alloc_copy_ptr_to_unchecked(data)
    }

    #[cfg(feature = "metadata")]
    /// Allocates and copies an unsized `T` by raw pointer without requiring
    /// `T: `[`UnsizedCopy`](crate::marker::UnsizedCopy), returning a `NonNull<T>`.
    ///
    /// # Safety
    ///
    /// - Callers must ensure `data` is safe to copy.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.size() == 0`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_copy_ptr_to_unchecked<T: ?Sized>(
        &self,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        alloc_then(self, unsafe { data.layout() }, data, |p, data| {
            ptr::copy_nonoverlapping(data.cast::<u8>(), p.as_ptr(), data.size());
            NonNull::from_raw_parts(p, data.metadata())
        })
    }

    /// Allocates memory for an uninitialized `T` and returns an [`AllocGuard`] around it to ensure
    /// deallocation on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[cfg_attr(miri, track_caller)]
    fn alloc_guard<T>(&'_ self) -> Result<AllocGuard<'_, T, Self>, AllocError> {
        alloc_then(self, T::LAYOUT, (), |p, ()| {
            // SAFETY: we just allocated the memory using `self`
            unsafe { AllocGuard::new(p.cast::<T>(), self) }
        })
    }

    #[cfg(feature = "metadata")]
    /// Allocates memory for a copy of `data` and returns an [`AllocGuard`] around it to ensure
    /// deallocation on panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    ///
    /// # Safety
    ///
    /// Callers must ensure `data` is a valid pointer.
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_guard_for<T: ?Sized>(
        &self,
        data: *const T,
    ) -> Result<AllocGuard<'_, T, Self>, AllocError> {
        alloc_then(self, unsafe { data.layout() }, data, |p, data| unsafe {
            AllocGuard::new(
                NonNull::new_unchecked(crate::unstable_util::with_meta(p.as_ptr(), data)),
                self,
            )
        })
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
