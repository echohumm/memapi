use crate::{
    error::AllocError,
    Alloc,
};
use alloc::alloc::Layout;
use core::ptr::{self, NonNull};

/// Trait for allocators that support allocating memory aligned at a specific offset.
///
/// This trait provides functions which perform actual allocations with an unspecified alignment,
/// including extra `offset` bytes before the requested allocation to align the request.
///
/// This is space-inefficient, but can be faster or provide space before the requested allocation
/// for an unaligned header.
pub trait AllocAlignedAt: Alloc {
    /// Attempts to allocate a block of memory fitting the given [`Layout`], aligned only after
    /// `offset` bytes.
    ///
    /// Note that the returned pointer itself will **not** be aligned to the layout's alignment.
    /// Instead, `ptr.add(offset)` will be.
    ///
    /// The memory pointed to by the returned pointer will be able to store an `offset` bytes header
    /// (unaligned) and the actual data (aligned to `layout.align()`).
    ///
    /// The returned layout must be used instead of `layout` to deallocate later.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    fn alloc_at(&self, layout: Layout, offset: usize) -> Result<(NonNull<u8>, Layout), AllocError>;

    /// Attempts to allocate a block of zeroed memory fitting the given [`Layout`], aligned only
    /// after `offset` bytes.
    ///
    /// Note that the returned pointer itself will **not** be aligned to the layout's alignment.
    /// Instead, `ptr.add(offset)` will be.
    ///
    /// The memory pointed to by the returned pointer will be able to store an `offset` bytes header
    /// (unaligned) and the actual data (aligned to `layout.align()`).
    ///
    /// The returned layout must be used instead of `layout` to deallocate later.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    /// - [`AllocError::InvalidLayout`] if the computed layout is invalid.
    fn zalloc_at(
        &self,
        layout: Layout,
        offset: usize,
    ) -> Result<(NonNull<u8>, Layout), AllocError> {
        let mem = tri!(do self.alloc_at(layout, offset));

        // SAFETY: the memory's actual size will be at least the size of the returned layout
        unsafe {
            ptr::write_bytes(mem.0.as_ptr(), 0, mem.1.size());
        }

        Ok(mem)
    }
}
