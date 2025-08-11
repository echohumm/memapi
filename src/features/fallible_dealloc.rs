use crate::{error::AllocError, Alloc};
use alloc::alloc::Layout;
use core::{
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    ptr::NonNull,
};

/// A trait for fallible deallocations.
pub trait FallibleDealloc: Alloc {
    /// Attempts to deallocate a previously allocated block.
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure or when the provided block is
    /// [invalid](BlockStatus).
    fn try_dealloc(&self, _: NonNull<u8>, _: Layout) -> Result<(), AllocError>;

    /// Returns the ownership status of the provided block.
    fn status(&self, ptr: NonNull<u8>, layout: Layout) -> BlockStatus;

    /// Returns whether the provided pointer is owned by this allocator.
    fn owns(&self, p: NonNull<u8>) -> bool;
}

// TODO: helpers for implementing this like `ptr_max_align(NonNull<u8>) -> usize`
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
    Misaligned(Option<usize>),

    /// The block is owned by this allocator.
    Owned,
}

impl Display for BlockStatus {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            BlockStatus::Owned => write!(f, "owned"),

            BlockStatus::Misaligned(Some(max_align)) => {
                write!(f, "owned (misaligned, max alignment: {})", max_align)
            }
            BlockStatus::Misaligned(None) => {
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
