use crate::{
    error::AllocError,
    grow,
    helpers::{alloc_then, AllocGuard},
    ralloc,
    type_props::{PtrProps, SizedProps},
    Alloc, AllocPattern,
};
use alloc::alloc::Layout;
use core::ptr::{self, NonNull};

#[cfg(feature = "fallible_dealloc")]
pub use crate::features::fallible_dealloc::ext::DeallocCheckedExt;

/// This trait provides methods for the core [`Alloc`] trait, providing convenient routines to
/// allocate, initialize, clone, copy, and deallocate sized and unsized types.
///
/// These helpers simplify common allocation patterns by combining `alloc`, writes, drops, and
/// deallocations for various data shapes.
pub trait AllocExt: Alloc {
    /// Allocates memory for a single `T` and initializes it using `init`.
    ///
    /// If `init` panics, the allocation will be deallocated.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[track_caller]
    #[inline]
    fn alloc_init<T, I: Fn(NonNull<T>)>(&self, init: I) -> Result<NonNull<T>, AllocError> {
        let guard = tri!(do self.alloc_guard());
        init(*guard);
        Ok(guard.release())
    }

    /// Allocates memory for a single `T` and writes `T`'s default into it.
    ///
    /// This is equivalent to `alloc.`[`walloc`](Self::walloc)`(T::default())`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[track_caller]
    #[inline]
    fn alloc_default<T: Default>(&self) -> Result<NonNull<T>, AllocError> {
        self.walloc(T::default())
    }

    /// Allocates memory for a single `T` and writes `data` into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn walloc<T>(&self, data: T) -> Result<NonNull<T>, AllocError> {
        // SAFETY: we just allocated the pointer using `T`'s layout, so it's safe to write `data` to
        // it
        alloc_then::<NonNull<T>, Self, T, _>(self, T::LAYOUT, data, |p, data| unsafe {
            let ptr: NonNull<T> = p.cast();
            ptr::write(ptr.as_ptr(), data);
            ptr
        })
    }

    #[cfg(not(feature = "clone_to_uninit"))]
    /// Allocates memory for a single `T` and clones `data` into it.
    ///
    /// This is equivalent to `alloc.`[`walloc`](Self::walloc)`(data.clone()))`
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `T::SZ == 0`.
    #[track_caller]
    #[inline]
    fn alloc_clone_to<T: Clone>(&self, data: &T) -> Result<NonNull<T>, AllocError> {
        // this implementation is better than the original as it defers allocation until after the
        //  clone succeeds, improving performance and removing the guard.
        self.walloc(data.clone())
    }

    #[cfg(all(feature = "clone_to_uninit", feature = "metadata"))]
    /// Allocates memory for a copy of the value behind `data` and clones the value into it using
    /// [`CloneToUninit`](core::clone::CloneToUninit).
    ///
    /// The clone operation may panic.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[track_caller]
    fn alloc_clone_to<T: core::clone::CloneToUninit + ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        // SAFETY: `data` is a reference that immediately fulfills `layout()`'s invariants;
        //  the pointer was just allocated by this allocator, is valid for writes of at
        //  least `data`'s size, and aligned.
        unsafe {
            alloc_then(self, data.layout(), data, |p, data| {
                let guard = AllocGuard::new(
                    NonNull::new_unchecked(crate::unstable_util::with_meta(p.as_ptr(), data)),
                    self,
                );
                data.clone_to_uninit(guard.as_ptr().cast::<u8>());
                guard.release()
            })
        }
    }

    #[cfg(all(feature = "clone_to_uninit", not(feature = "metadata")))]
    /// Allocates memory for a copy of the value behind `data` and clones the value into it using
    /// [`CloneToUninit`](core::clone::CloneToUninit).
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[track_caller]
    fn alloc_clone_to<T: core::clone::CloneToUninit + crate::type_props::VarSized + ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        // SAFETY: `data` is a reference that immediately fulfills `layout()`'s invariants;
        //  we just allocated the pointer using `self`;
        //  what's returned by sz will be the metadata of the type as it's VarSized.
        unsafe {
            alloc_then::<NonNull<T>, Self, &T, _>(self, data.layout(), data, |p, data| {
                let guard = AllocGuard::new(
                    crate::type_props::varsized_nonnull_from_raw_parts::<T>(p, data.sz()),
                    self,
                );
                data.clone_to_uninit(guard.as_ptr().cast());
                guard.release()
            })
        }
    }

    /// Attempts to allocate a block of memory fitting the given [`Layout`], filled with bytes
    /// initialized to `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout.size() == 0`
    #[cfg_attr(miri, track_caller)]
    fn falloc(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError> {
        // SAFETY: allocation returns at least `layout.size()` bytes
        alloc_then::<NonNull<u8>, Self, u8, _>(self, layout, n, |p, n| unsafe {
            ptr::write_bytes(p.as_ptr(), n, layout.size());
            p
        })
    }

    /// Drops the data at a pointer and deallocates its previously allocated block.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - point to a block of memory allocated using this allocator
    /// - be valid for reads and writes
    /// - be properly aligned
    /// - point to a valid `T`
    #[track_caller]
    #[inline]
    unsafe fn drop_and_dealloc<T: ?Sized>(&self, ptr: NonNull<T>) {
        ptr::drop_in_place(ptr.as_ptr());
        self.dealloc_typed(ptr);
    }

    /// Zeroes and deallocates the memory at a pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must:
    ///   - point to a block of memory allocated using this allocator.
    ///   - be valid for writes of `layout.size()` bytes
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
    /// `ptr` must:
    /// - point to a block of memory allocated using this allocator.
    /// - have correct metadata for its type
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc_typed<T: ?Sized>(&self, ptr: NonNull<T>) {
        self.dealloc(ptr.cast::<u8>(), ptr.layout());
    }

    /// Zeroes and deallocates the memory at a pointer.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - point to a block of memory allocated using this allocator.
    /// - have correct metadata for its type
    /// - be valid for writes of `ptr.`[`sz`](PtrProps::sz)`()` bytes
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zero_and_dealloc_typed<T: ?Sized>(&self, ptr: NonNull<T>) {
        ptr::write_bytes(ptr.as_ptr().cast::<u8>(), 0, ptr.sz());
        self.dealloc_typed(ptr);
    }

    /// Drops the value at the given pointer, then zeroes and deallocates its memory.
    ///
    /// # Safety
    ///
    /// `ptr` must:
    /// - point to a block of memory allocated using this allocator
    /// - be valid for reads, and writes of `ptr.`[`sz`](PtrProps::sz)`()` bytes
    /// - be properly aligned
    /// - point to a valid `T`
    #[track_caller]
    #[inline]
    unsafe fn drop_zero_and_dealloc<T: ?Sized>(&self, ptr: NonNull<T>) {
        ptr::drop_in_place(ptr.as_ptr());
        self.zero_and_dealloc_typed(ptr);
    }

    #[cfg(feature = "metadata")]
    /// Allocates memory for a copy of the value behind `data`, then copies the value into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[cfg_attr(miri, track_caller)]
    fn alloc_copy_ref_to<T: ?Sized + crate::marker::UnsizedCopy>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        // SAFETY: `T: Copy`
        unsafe { self.alloc_copy_ref_to_unchecked(data) }
    }

    #[cfg(feature = "metadata")]
    /// Allocates memory for a copy of the value behind `data`, then copies the value into it.
    ///
    /// # Safety
    ///
    /// Callers must ensure `data` is a valid pointer to copy from.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_copy_ptr_to<T: ?Sized + crate::marker::UnsizedCopy>(
        &self,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        // SAFETY: `T: Copy`
        unsafe { self.alloc_copy_ptr_to_unchecked(data) }
    }

    #[cfg(feature = "metadata")]
    /// Allocates memory for a copy of the value behind `data`, then copies the value into it.
    ///
    /// This variant doesn't require `T: `[`UnsizedCopy`](crate::marker::UnsizedCopy).
    ///
    /// # Safety
    ///
    /// Callers must ensure `data` is safe to copy.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_copy_ref_to_unchecked<T: ?Sized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        self.alloc_copy_ptr_to_unchecked(data)
    }

    #[cfg(feature = "metadata")]
    /// Allocates memory for a copy of the value behind `data`, then copies the value into it.
    ///
    /// This variant doesn't require `T: `[`UnsizedCopy`](crate::marker::UnsizedCopy).
    ///
    /// # Safety
    ///
    /// Callers must ensure `data` is safe to copy.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_copy_ptr_to_unchecked<T: ?Sized>(
        &self,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        // SAFETY: the caller guarantees `data` is valid.
        alloc_then(self, data.layout(), data, |p, data| {
            ptr::copy_nonoverlapping(data.cast::<u8>(), p.as_ptr(), data.sz());
            NonNull::from_raw_parts(p, data.metadata())
        })
    }

    #[cfg(not(feature = "metadata"))]
    /// Allocates memory for a copy of the value behind `data`, then copies the value into it.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[cfg_attr(miri, track_caller)]
    fn alloc_copy_ref_to<T: ?Sized + crate::type_props::VarSized + crate::marker::UnsizedCopy>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        // SAFETY: `T: Copy`
        unsafe { self.alloc_copy_ref_to_unchecked(data) }
    }

    #[cfg(not(feature = "metadata"))]
    /// Allocates memory for a copy of the value behind `data`, then copies the value into it.
    ///
    /// # Safety
    ///
    /// Callers must ensure `data` is a valid pointer to copy from.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_copy_ptr_to<
        T: ?Sized + crate::type_props::VarSized + crate::marker::UnsizedCopy,
    >(
        &self,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        // SAFETY: `T: Copy`
        self.alloc_copy_ptr_to_unchecked(data)
    }

    #[cfg(not(feature = "metadata"))]
    /// Allocates memory for a copy of the value behind `data`, then copies the value into it.
    ///
    /// This variant doesn't require `T: `[`UnsizedCopy`](crate::marker::UnsizedCopy).
    ///
    /// # Safety
    ///
    /// Callers must ensure `data` is safe to copy.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_copy_ref_to_unchecked<T: ?Sized + crate::type_props::VarSized>(
        &self,
        data: &T,
    ) -> Result<NonNull<T>, AllocError> {
        self.alloc_copy_ptr_to_unchecked(data)
    }

    #[cfg(not(feature = "metadata"))]
    /// Allocates memory for a copy of the value behind `data`, then copies the value into it.
    ///
    /// This variant doesn't require `T: `[`UnsizedCopy`](crate::marker::UnsizedCopy).
    ///
    /// # Safety
    ///
    /// Callers must ensure `data` is safe to copy.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_copy_ptr_to_unchecked<T: ?Sized + crate::type_props::VarSized>(
        &self,
        data: *const T,
    ) -> Result<NonNull<T>, AllocError> {
        // SAFETY: the caller guarantees `data` is valid.
        alloc_then(self, data.layout(), data, |p, data| {
            ptr::copy_nonoverlapping(data.cast::<u8>(), p.as_ptr(), data.sz());
            crate::type_props::varsized_nonnull_from_raw_parts(p, data.sz())
        })
    }

    /// Allocates memory for a `T` and returns an [`AllocGuard`] around it to ensure deallocation on
    /// panic.
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
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[cfg_attr(miri, track_caller)]
    fn alloc_guard_for_ref<T: ?Sized>(
        &self,
        data: &T,
    ) -> Result<AllocGuard<'_, T, Self>, AllocError> {
        // SAFETY: all references are valid pointers
        unsafe { self.alloc_guard_for_ptr(data) }
    }

    #[cfg(feature = "metadata")]
    /// Allocates memory for a copy of `data` and returns an [`AllocGuard`] around it to ensure
    /// deallocation on panic.
    ///
    /// # Safety
    ///
    /// Callers must ensure `data` is a valid pointer.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `data.sz() == 0`.
    #[cfg_attr(miri, track_caller)]
    unsafe fn alloc_guard_for_ptr<T: ?Sized>(
        &self,
        data: *const T,
    ) -> Result<AllocGuard<'_, T, Self>, AllocError> {
        // SAFETY: we just allocated the memory using `self`, the caller guarantees `data` is valid
        alloc_then(self, data.layout(), data, |p, data| {
            AllocGuard::new(
                NonNull::new_unchecked(crate::unstable_util::with_meta(p.as_ptr(), data)),
                self,
            )
        })
    }

    /// Grows the given block to a new, larger layout, filling any newly allocated bytes with `n`.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout.size() == 0`
    #[cfg_attr(miri, track_caller)]
    unsafe fn fgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<NonNull<u8>, AllocError> {
        grow(self, ptr, old_layout, new_layout, AllocPattern::Filled(n))
    }

    /// Reallocate a block, growing or shrinking as needed, filling any newly
    /// allocated bytes with `n`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout.size()` == 0
    #[cfg_attr(miri, track_caller)]
    unsafe fn refalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<NonNull<u8>, AllocError> {
        ralloc(self, ptr, old_layout, new_layout, AllocPattern::Filled(n))
    }
}

impl<A: Alloc + ?Sized> AllocExt for A {}
