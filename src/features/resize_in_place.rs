use crate::{error::AllocError, helpers::SliceAllocGuard, Alloc};
use core::{
    alloc::Layout,
    ptr::{self, NonNull},
};

/// Extension trait for [`Alloc`](Alloc) which provides interfaces to reallocate in-place.
pub trait ResizeInPlace: Alloc {
    /// Grow the given block to a new, larger layout.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_size < old_layout.size()`.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the growth operation could not be
    ///   completed in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[cfg_attr(miri, track_caller)]
    unsafe fn grow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError>;

    /// Grow the given block to a new, larger layout, zeroing newly allocated bytes.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_size < old_layout.size()`.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the growth operation could not be
    ///   completed in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[cfg_attr(miri, track_caller)]
    unsafe fn grow_in_place_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        self.grow_in_place_filled(ptr, old_layout, new_size, 0)
    }

    /// Grow the given block to a new, larger layout, filling any newly allocated bytes by calling
    /// `pattern(i)` for each new byte index `i`.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_size < old_layout.size()`.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the growth operation could not be
    ///   completed in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[cfg_attr(miri, track_caller)]
    unsafe fn grow_in_place_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
        pattern: F,
    ) -> Result<(), AllocError> {
        self.grow_in_place(ptr, old_layout, new_size)?;

        let start_idx = old_layout.size();
        let mut start = SliceAllocGuard::new(
            NonNull::new_unchecked(ptr.as_ptr().add(start_idx)),
            &self,
            new_size - start_idx,
        );

        for i in 0..new_size - start_idx {
            start.init_unchecked(pattern(start_idx + i));
        }
        Ok(())
    }

    /// Grow the given block to a new, larger layout, filling any newly allocated bytes with `n`.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_size < old_layout.size()`.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the growth operation could not be
    ///   completed in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[cfg_attr(miri, track_caller)]
    unsafe fn grow_in_place_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
        n: u8,
    ) -> Result<(), AllocError> {
        self.grow_in_place(ptr, old_layout, new_size)?;
        ptr::write_bytes(
            ptr.as_ptr().add(old_layout.size()),
            n,
            new_size - old_layout.size(),
        );
        Ok(())
    }

    /// Shrink the given block to a new, smaller layout.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_size > old_layout.size()`.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the shrink operation could not be
    ///   completed in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[cfg_attr(miri, track_caller)]
    unsafe fn shrink_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError>;

    /// Reallocate a block, growing or shrinking as needed.
    ///
    /// On grow, preserves existing contents up to `old_layout.size()`, and
    /// on shrink, truncates to `new_size`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the reallocation operation could not
    ///   be completed in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[cfg_attr(miri, track_caller)]
    unsafe fn realloc_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size > old_layout.size() {
            self.grow_in_place(ptr, old_layout, new_size)
        } else {
            self.shrink_in_place(ptr, old_layout, new_size)
        }
    }

    /// Reallocate a block, growing or shrinking as needed, zeroing any newly allocated bytes.
    ///
    /// On grow, preserves existing contents up to `old_layout.size()`, and
    /// on shrink, truncates to `new_size`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the reallocation operation could not
    ///   be completed in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[cfg_attr(miri, track_caller)]
    unsafe fn realloc_in_place_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size > old_layout.size() {
            self.grow_in_place_zeroed(ptr, old_layout, new_size)
        } else {
            self.shrink_in_place(ptr, old_layout, new_size)
        }
    }

    /// Reallocate a block, growing or shrinking as needed, filling any new bytes by calling
    /// `pattern(i)` for each new byte index `i`.
    ///
    /// On grow, preserves existing contents up to `old_layout.size()`, and
    /// on shrink, truncates to `new_size`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the reallocation operation could not
    ///   be completed in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[cfg_attr(miri, track_caller)]
    unsafe fn realloc_in_place_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
        pattern: F,
    ) -> Result<(), AllocError> {
        if new_size > old_layout.size() {
            self.grow_in_place_patterned(ptr, old_layout, new_size, pattern)
        } else {
            self.shrink_in_place(ptr, old_layout, new_size)
        }
    }

    /// Reallocate a block, growing or shrinking as needed, filling any newly allocated bytes with
    /// `n`.
    ///
    /// On grow, preserves existing contents up to `old_layout.size()`, and
    /// on shrink, truncates to `new_size`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the reallocation operation could not
    ///   be completed in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[cfg_attr(miri, track_caller)]
    unsafe fn realloc_in_place_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
        n: u8,
    ) -> Result<(), AllocError> {
        if new_size > old_layout.size() {
            self.grow_in_place_filled(ptr, old_layout, new_size, n)
        } else {
            self.shrink_in_place(ptr, old_layout, new_size)
        }
    }
}

#[cfg(any(feature = "jemalloc", feature = "mimalloc"))]
const RESIZE_IP_ZS: &str = "zero-sized resize in place was requested";
#[cfg(any(feature = "jemalloc", feature = "mimalloc"))]
const CANNOT_RESIZE_IP: &str = "cannot resize in place";

#[cfg(feature = "jemalloc")]
impl ResizeInPlace for crate::external_alloc::jemalloc::Jemalloc {
    unsafe fn grow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(AllocError::Other(RESIZE_IP_ZS))
        } else if new_size < old_layout.size() {
            Err(AllocError::GrowSmallerNewLayout(
                old_layout.size(),
                new_size,
            ))
        } else {
            // it isn't my fault if this is wrong lol
            if crate::external_alloc::ffi::jem::xallocx(
                ptr.as_ptr().cast::<libc::c_void>(),
                new_size,
                0,
                crate::external_alloc::ffi::jem::layout_to_flags(new_size, old_layout.align()),
            ) >= new_size
            {
                Ok(())
            } else {
                Err(AllocError::Other(CANNOT_RESIZE_IP))
            }
        }
    }

    unsafe fn shrink_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(AllocError::Other(RESIZE_IP_ZS))
        } else if new_size > old_layout.size() {
            Err(AllocError::ShrinkBiggerNewLayout(
                old_layout.size(),
                new_size,
            ))
        } else if new_size == old_layout.size() {
            // noop
            Ok(())
        } else {
            let flags =
                crate::external_alloc::ffi::jem::layout_to_flags(new_size, old_layout.align());
            let usable_size = crate::external_alloc::ffi::jem::xallocx(
                ptr.as_ptr().cast::<libc::c_void>(),
                new_size,
                0,
                flags,
            );

            if usable_size < old_layout.size() {
                Ok(())
            } else if usable_size == crate::external_alloc::ffi::jem::nallocx(new_size, flags) {
                debug_assert_eq!(
                    crate::external_alloc::ffi::jem::nallocx(new_size, flags),
                    crate::external_alloc::ffi::jem::nallocx(old_layout.size(), flags)
                );

                Ok(())
            } else {
                Err(AllocError::Other(CANNOT_RESIZE_IP))
            }
        }
    }
}

#[cfg(feature = "mimalloc")]
pub(crate) const SHRINK_IP: &str = "unsupported operation: attempted to shrink in place";

#[cfg(feature = "mimalloc")]
impl ResizeInPlace for crate::external_alloc::mimalloc::MiMalloc {
    unsafe fn grow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(AllocError::Other(RESIZE_IP_ZS))
        } else if new_size < old_layout.size() {
            Err(AllocError::GrowSmallerNewLayout(
                old_layout.size(),
                new_size,
            ))
        } else {
            // this would be, though
            if crate::external_alloc::ffi::mim::mi_expand(
                ptr.as_ptr().cast::<libc::c_void>(),
                new_size,
            )
            .is_null()
            {
                Err(AllocError::Other(CANNOT_RESIZE_IP))
            } else {
                Ok(())
            }
        }
    }

    /// Shrinking in-place is not supported by mimalloc.
    ///
    /// This is a no-op and always returns an error.
    ///
    /// # Errors
    ///
    /// - [`AllocError::Other`]`("unsupported operation: attempted to shrink in place")`.
    // it just returns an error, no reason not to inline it.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    unsafe fn shrink_in_place(
        &self,
        _: NonNull<u8>,
        _: Layout,
        _: usize,
    ) -> Result<(), AllocError> {
        Err(AllocError::Other(SHRINK_IP))
    }
}

// TODO: the absolutely hellish task of adding in-place operations parallel to alloc_ext's and
//  alloc_slice's methods
