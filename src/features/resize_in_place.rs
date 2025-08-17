use crate::{error::AllocError, Alloc, Layout};
use core::ptr::{self, NonNull};

/// Extension trait for [`Alloc`](Alloc) which provides interfaces to reallocate in-place.
pub trait ResizeInPlace: Alloc {
    /// Grow the given block to a new, larger layout.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_size < old_layout.size()`.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the growth operation could not be
    ///   completed in-place.
    #[cfg_attr(miri, track_caller)]
    unsafe fn grow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError>;

    /// Grow the given block to a new, larger layout, zeroing newly allocated bytes.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_size < old_layout.size()`.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the growth operation could not be
    ///   completed in-place.
    #[cfg_attr(miri, track_caller)]
    unsafe fn zgrow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        self.fgrow_in_place(ptr, old_layout, new_size, 0)
    }

    /// Grow the given block to a new, larger layout, filling any newly allocated bytes with `n`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_size < old_layout.size()`.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the growth operation could not be
    ///   completed in-place.
    #[cfg_attr(miri, track_caller)]
    unsafe fn fgrow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
        n: u8,
    ) -> Result<(), AllocError> {
        tri!(do self.grow_in_place(ptr, old_layout, new_size));
        ptr::write_bytes(
            ptr.as_ptr().add(old_layout.size()),
            n,
            new_size - old_layout.size(),
        );
        Ok(())
    }

    /// Shrink the given block to a new, smaller layout.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ShrinkLargerNewLayout`] if `new_size > old_layout.size()`.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the shrink operation could not be
    ///   completed in-place.
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
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the reallocation operation could not
    ///   be completed in-place.
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
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the reallocation operation could not
    ///   be completed in-place.
    #[cfg_attr(miri, track_caller)]
    unsafe fn rezalloc_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size > old_layout.size() {
            self.zgrow_in_place(ptr, old_layout, new_size)
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
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::Other`]`("zero-sized resize in place was requested")` if `new_size` is zero.
    /// - [`AllocError::Other`]`("cannot resize in place")` if the reallocation operation could not
    ///   be completed in-place.
    #[cfg_attr(miri, track_caller)]
    unsafe fn refalloc_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
        n: u8,
    ) -> Result<(), AllocError> {
        if new_size > old_layout.size() {
            self.fgrow_in_place(ptr, old_layout, new_size, n)
        } else {
            self.shrink_in_place(ptr, old_layout, new_size)
        }
    }
}

#[cfg_attr(not(feature = "dev"), doc(hidden))]
pub const RESIZE_IP_ZS: AllocError = AllocError::Other("zero-sized resize in place was requested");
#[cfg_attr(not(feature = "dev"), doc(hidden))]
pub const CANNOT_RESIZE_IP: AllocError = AllocError::Other("can't resize in place");

// TODO: add methods parallel to the other extension traits' methods
