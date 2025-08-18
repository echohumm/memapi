use {
    crate::{Alloc, AllocPattern, Layout, error::AllocError, grow, helpers::alloc_then, ralloc},
    core::ptr::{self, NonNull}
};

/// This trait provides methods for the core [`Alloc`] trait, providing convenient routines to
/// allocate, initialize, clone, copy, and deallocate sized and unsized types.
///
/// These helpers simplify common, not entirely trivial allocation patterns.
pub trait AllocExt: Alloc {
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
    fn alloc_clone<T: Clone>(&self, data: &T) -> Result<NonNull<T>, AllocError> {
        // clone the data before allocating to avoid needing a guard
        let dup = data.clone();
        let mem = tri!(do self.alloc(<T as crate::type_props::SizedProps>::LAYOUT)).cast();
        // SAFETY: the pointer will have at least enough space for a `T`
        unsafe {
            ptr::write(mem.as_ptr(), dup);
        }
        Ok(mem)
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
    fn alloc_clone<T: core::clone::CloneToUninit + ?Sized>(
        &self,
        data: &T
    ) -> Result<NonNull<T>, AllocError> {
        // SAFETY: `data` is a reference that immediately fulfills `layout()`'s invariants;
        //  the pointer was just allocated by this allocator, is valid for writes of at
        //  least `data`'s size, and aligned.
        unsafe {
            alloc_then(self, crate::type_props::PtrProps::layout(&data), data, |p, data| {
                let guard = crate::helpers::AllocGuard::new(
                    NonNull::new_unchecked(crate::unstable_util::with_meta(p.as_ptr(), data)),
                    self
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
    fn alloc_clone<T: core::clone::CloneToUninit + crate::type_props::VarSized + ?Sized>(
        &self,
        data: &T
    ) -> Result<NonNull<T>, AllocError> {
        // SAFETY: `data` is a reference that immediately fulfills `layout()`'s invariants;
        //  we just allocated the pointer using `self`;
        //  what's returned by sz will be the metadata of the type as it's VarSized.
        unsafe {
            alloc_then::<NonNull<T>, Self, &T, _>(
                self,
                crate::type_props::PtrProps::layout(&data),
                data,
                |p, data| {
                    let guard = crate::helpers::AllocGuard::new(
                        crate::type_props::varsized_nonnull_from_raw_parts::<T>(
                            p,
                            crate::type_props::PtrProps::sz(&data)
                        ),
                        self
                    );
                    data.clone_to_uninit(guard.as_ptr().cast());
                    guard.release()
                }
            )
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
        n: u8
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
        n: u8
    ) -> Result<NonNull<u8>, AllocError> {
        ralloc(self, ptr, old_layout, new_layout, AllocPattern::Filled(n))
    }
}

impl<A: Alloc + ?Sized> AllocExt for A {}
