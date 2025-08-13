use crate::{error::AllocError, Alloc};
use alloc::alloc::Layout;
use core::{
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    ptr::NonNull,
};

/// A trait for allocators to perform deallocations without checking for validity.
///
/// `memapi`'s main deallocation function checks whether the `layout` it recieves is zero-sized.
/// This does not.
pub trait DeallocUnchecked: Alloc {
    /// Deallocates a previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `layout` must describe exactly the same block.
    /// - depending on the underlying allocator, `layout` shouldn't be zero-sized.
    unsafe fn dealloc_unchecked(&self, ptr: NonNull<u8>, layout: Layout);
}

/// A trait for allocators to attempt deallocation.
pub trait DeallocChecked: DeallocUnchecked {
    /// Attempts to deallocate a previously allocated block.
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](BlockStatus), or if the provided layout is zero-sized.
    fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), AllocError> {
        match self.status(ptr, layout) {
            // SAFETY: the pointer is owned by us, and the layout is valid and non-zero-sized.
            BlockStatus::Owned => unsafe {
                self.dealloc_unchecked(ptr, layout);
                Ok(())
            },
            other => Err(AllocError::DeallocFailed(
                ptr,
                layout,
                crate::error::Cause::InvalidBlockStatus(other),
            )),
        }
    }

    /// Returns the ownership status of the provided block.
    fn status(&self, ptr: NonNull<u8>, layout: Layout) -> BlockStatus;

    /// Returns whether the provided pointer is owned by this allocator.
    fn owns(&self, ptr: NonNull<u8>) -> bool;
}

/// Returns the maximum alignment satisfied by a non-null pointer.
#[must_use]
pub fn ptr_max_align(ptr: NonNull<u8>) -> usize {
    let p = ptr.as_ptr() as usize;
    
    p & p.wrapping_neg()
}

/// The status of a block.
///
/// [`Owned`](BlockStatus::Owned) signifies the block is valid to deallocate. All other variants are
/// an error.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BlockStatus {
    /// The block is neither owned by this allocator nor has an alignment matching the provided
    /// layout's.
    ///
    /// If `self.0` is `Some`, it is the maximum alignment the provided pointer fulfills.
    /// Otherwise, the implementation doesn't support returning the block's alignment.
    NotOwnedMisaligned(Option<usize>),

    /// The block is not owned by this allocator.
    NotOwned,

    /// The block is owned by this allocator, but the provided pointer is not the start of the
    /// block.
    ///
    /// If `self.0` is `Some`, it is the pointer to the start of the block.
    /// Otherwise, the implementation doesn't support returning the block's start, or an error
    /// occurred fetching it.
    OwnedNonHead(Option<NonNull<u8>>),

    /// The block is owned by this allocator, but the provided layout doesn't match the full block.
    ///
    /// If `self.0` is `Some`, it is the layout of the full block.
    /// Otherwise, the implementation doesn't support returning the block's full layout, or an error
    /// occurred fetching it.
    OwnedIncomplete(Option<Layout>),

    /// The block is owned by this allocator, but its alignment is less than the provided layout's.
    ///
    /// If `self.0` is `Some`, it is the maximum alignment the provided pointer fulfills.
    /// Otherwise, the implementation doesn't support returning the block's alignment.
    OwnedMisaligned(Option<usize>),

    /// The block is owned by this allocator.
    Owned,
}

impl Display for BlockStatus {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            BlockStatus::Owned => write!(f, "owned"),

            BlockStatus::OwnedMisaligned(Some(max_align)) => {
                write!(f, "owned (misaligned, max alignment: {})", max_align)
            }
            BlockStatus::OwnedMisaligned(None) => {
                write!(f, "owned (misaligned, max alignment: unknown)")
            }

            BlockStatus::OwnedIncomplete(Some(layout)) => {
                write!(f, "owned (incomplete, full layout: {:?})", layout)
            }
            BlockStatus::OwnedIncomplete(None) => {
                write!(f, "owned (incomplete, full layout: unknown)")
            }

            BlockStatus::OwnedNonHead(Some(ptr)) => {
                write!(f, "owned (non-head, block start: {:p})", *ptr)
            }
            BlockStatus::OwnedNonHead(None) => write!(f, "owned (non-head, block start: unknown)"),

            BlockStatus::NotOwned => write!(f, "not owned"),

            BlockStatus::NotOwnedMisaligned(Some(max_align)) => {
                write!(f, "not owned (misaligned, max alignment: {})", max_align)
            }
            BlockStatus::NotOwnedMisaligned(None) => {
                write!(f, "not owned (misaligned, max alignment: unknown)")
            }
        }
    }
}
