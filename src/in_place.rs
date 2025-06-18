#![allow(missing_docs)]

use crate::{error::AllocError, Alloc};
use core::{alloc::Layout, ptr::NonNull};

pub trait ResizeInPlace: Alloc {
    /// Grow the given block to a new, larger layout.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_size < old_layout.size()`.
    /// - [`AllocError::ResizeInPlaceZeroSized`] if `new_size` is zero.
    /// - [`AllocError::CannotResizeInPlace`] if the growth operation could not be completed
    ///   in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
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
    /// - [`AllocError::ResizeInPlaceZeroSized`] if `new_size` is zero.
    /// - [`AllocError::CannotResizeInPlace`] if the growth operation could not be completed
    ///   in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    #[inline]
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
    /// - [`AllocError::ResizeInPlaceZeroSized`] if `new_size` is zero.
    /// - [`AllocError::CannotResizeInPlace`] if the growth operation could not be completed
    ///   in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    #[inline]
    unsafe fn grow_in_place_patterned<F: Fn(usize) -> u8 + Clone>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
        pattern: F,
    ) -> Result<(), AllocError> {
        self.grow_in_place(ptr, old_layout, new_size)?;
        let start_num = old_layout.size();
        let start = ptr.add(start_num);
        for i in 0..new_size - old_layout.size() {
            start.add(i).write(pattern(start_num + i));
        }
        Ok(())
    }

    /// Grow the given block to a new, larger layout, filling any newly allocated bytes with `n`.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_size < old_layout.size()`.
    /// - [`AllocError::ResizeInPlaceZeroSized`] if `new_size` is zero.
    /// - [`AllocError::CannotResizeInPlace`] if the growth operation could not be completed
    ///   in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    #[inline]
    unsafe fn grow_in_place_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
        n: u8,
    ) -> Result<(), AllocError> {
        self.grow_in_place(ptr, old_layout, new_size)?;
        ptr.add(old_layout.size())
            .write_bytes(n, new_size - old_layout.size());
        Ok(())
    }

    /// Shrink the given block to a new, smaller layout.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_layout.size() > old_layout.size()`.
    /// - [`AllocError::ResizeInPlaceZeroSized`] if `new_size` is zero.
    /// - [`AllocError::CannotResizeInPlace`] if the shrink operation could not be completed
    ///   in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
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
    /// - [`AllocError::ResizeInPlaceZeroSized`] if `new_layout` has a size of zero.
    /// - [`AllocError::CannotResizeInPlace`] if the reallocation operation could not be completed
    ///   in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
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
    /// - [`AllocError::ResizeInPlaceZeroSized`] if `new_layout` has a size of zero.
    /// - [`AllocError::CannotResizeInPlace`] if the reallocation operation could not be completed
    ///   in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
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
    /// - [`AllocError::ResizeInPlaceZeroSized`] if `new_layout` has a size of zero.
    /// - [`AllocError::CannotResizeInPlace`] if the reallocation operation could not be completed
    ///   in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
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
    /// - [`AllocError::ResizeInPlaceZeroSized`] if `new_layout` has a size of zero.
    /// - [`AllocError::CannotResizeInPlace`] if the reallocation operation could not be completed
    ///   in-place.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    #[inline]
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

#[cfg(feature = "jemalloc_in_place")]
impl ResizeInPlace for crate::external_alloc::jemalloc::Jemalloc {
    #[inline]
    unsafe fn grow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(AllocError::ResizeInPlaceZeroSized)
        } else if new_size < old_layout.size() {
            Err(AllocError::GrowSmallerNewLayout(
                old_layout.size(),
                new_size,
            ))
        } else {
            // it isn't my fault if this is wrong lol
            if crate::external_alloc::ffi::jem::xallocx(
                ptr.as_ptr().cast(),
                new_size,
                0,
                crate::external_alloc::ffi::jem::layout_to_flags(new_size, old_layout.align()),
            ) >= new_size
            {
                Ok(())
            } else {
                Err(AllocError::CannotResizeInPlace)
            }
        }
    }

    #[inline]
    unsafe fn shrink_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(AllocError::ResizeInPlaceZeroSized)
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
            let usable_size =
                crate::external_alloc::ffi::jem::xallocx(ptr.as_ptr().cast(), new_size, 0, flags);

            if usable_size < old_layout.size() {
                Ok(())
            } else if usable_size == crate::external_alloc::ffi::jem::nallocx(new_size, flags) {
                debug_assert_eq!(
                    crate::external_alloc::ffi::jem::nallocx(new_size, flags),
                    crate::external_alloc::ffi::jem::nallocx(old_layout.size(), flags)
                );

                Ok(())
            } else {
                Err(AllocError::CannotResizeInPlace)
            }
        }
    }
}

#[cfg(feature = "mimalloc_in_place")]
impl ResizeInPlace for crate::external_alloc::mimalloc::MiMalloc {
    #[inline]
    unsafe fn grow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_size: usize,
    ) -> Result<(), AllocError> {
        if new_size == 0 {
            Err(AllocError::ResizeInPlaceZeroSized)
        } else if new_size < old_layout.size() {
            Err(AllocError::GrowSmallerNewLayout(
                old_layout.size(),
                new_size,
            ))
        } else {
            // this would be, though
            if crate::external_alloc::ffi::mim::mi_expand(ptr.as_ptr().cast(), new_size).is_null() {
                Err(AllocError::CannotResizeInPlace)
            } else {
                Ok(())
            }
        }
    }

    unsafe fn shrink_in_place(
        &self,
        _: NonNull<u8>,
        _: Layout,
        _: usize,
    ) -> Result<(), AllocError> {
        Err(AllocError::UnsupportedOperation(
            crate::error::UOp::ShrinkInPlace,
        ))
    }
}
