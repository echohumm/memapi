use {
    crate::{Alloc, Layout, error::AllocError},
    core::ptr::{self, NonNull}
};

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
        offset: usize
    ) -> Result<(NonNull<u8>, Layout), AllocError> {
        let mem = tri!(do self.alloc_at(layout, offset));

        // SAFETY: the memory's actual size will be at least the size of the returned layout
        unsafe {
            ptr::write_bytes(mem.0.as_ptr(), 0, mem.1.size());
        }

        Ok(mem)
    }
}

#[cfg(feature = "alloc_ext")]
/// This trait provides extensions for [`AllocAlignedAt`].
#[allow(clippy::module_name_repetitions)]
pub trait AllocAlignedAtExt: AllocAlignedAt {
    /// Attempts to allocate a block of memory fitting the given [`Layout`], aligned only after
    /// `offset` bytes, then fill it according to [`sector`](AlignedAtSectorDescriptor).
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
    #[cfg_attr(miri, track_caller)]
    fn falloc_at(
        &self,
        layout: Layout,
        offset: usize,
        sector: AlignedAtSectorDescriptor
    ) -> Result<(NonNull<u8>, Layout), AllocError> {
        match self.alloc_at(layout, offset) {
            Ok((p, act_layout)) => {
                let ptr = p.as_ptr();
                // SAFETY: allocation returns at least `layout.size() + offset` bytes
                unsafe {
                    match sector {
                        AlignedAtSectorDescriptor::Header(b) => {
                            ptr::write_bytes(ptr, b, offset);
                        }
                        AlignedAtSectorDescriptor::Data(b) => {
                            ptr::write_bytes(ptr.add(offset), b, act_layout.size() - offset);
                        }
                        AlignedAtSectorDescriptor::Both(b) => {
                            ptr::write_bytes(ptr, b, act_layout.size());
                        }
                        AlignedAtSectorDescriptor::Separate(h, d) => {
                            ptr::write_bytes(ptr, h, offset);
                            ptr::write_bytes(ptr.add(offset), d, act_layout.size() - offset);
                        }
                    }
                }
                Ok((p, act_layout))
            }
            Err(e) => Err(e)
        }
    }
}

// TODO: make this better, maybe use something similar elsewhere
#[cfg(feature = "alloc_ext")]
/// Which sector of the allocation to fill with what byte.
#[derive(Debug, Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
#[repr(u8)]
// unfortunately, very verbose name because this gets re-exported at the root. (TOFIX)
pub enum AlignedAtSectorDescriptor {
    /// Fill the header with the contained byte.
    Header(u8),
    /// Fill the data with the contained byte.
    Data(u8),
    /// Fill both the header and the data with the contained byte.
    Both(u8),
    /// Fill the header with the first byte and the data with the second byte.
    Separate(u8, u8)
}

#[cfg(feature = "alloc_ext")]
impl<A: AllocAlignedAt> AllocAlignedAtExt for A {}
