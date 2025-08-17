use crate::{error::AllocError, Alloc, Layout};
use core::{
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    ptr::NonNull,
};

#[cfg(feature = "alloc_ext")]
pub(crate) mod ext;
#[cfg(feature = "alloc_ext")]
pub use ext::DeallocCheckedExt;

#[cfg(feature = "alloc_slice")]
pub(crate) mod slice;
#[cfg(feature = "alloc_slice")]
pub use slice::DeallocCheckedSlice;
#[cfg(all(feature = "alloc_slice", feature = "alloc_ext"))]
pub use slice::DeallocCheckedSliceExt;

/// A trait for allocators to attempt deallocation.
pub trait DeallocChecked: Alloc {
    /// Attempts to deallocate a previously allocated block.
    ///
    /// # Errors
    ///
    /// Implementations may return `Err` on deallocation failure, when the provided block is
    /// [invalid](BlockStatus), or if the provided layout is zero-sized.
    fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), AllocError> {
        // SAFETY: the pointer is owned by us, and the layout is valid and non-zero-sized.
        base_try_dealloc_impl(self, ptr, layout, |d, p, l| unsafe {
            Self::dealloc(d, p.cast::<u8>(), l);
        })
    }

    /// Returns the ownership status of the provided block.
    fn status(&self, ptr: NonNull<u8>, layout: Layout) -> BlockStatus;

    /// Returns whether this allocator owns the provided pointer.
    fn owns(&self, ptr: NonNull<u8>) -> bool;
}

#[allow(clippy::inline_always)]
impl<D: DeallocChecked + ?Sized> DeallocChecked for &D {
    #[inline(always)]
    fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), AllocError> {
        (**self).try_dealloc(ptr, layout)
    }

    #[inline(always)]
    fn status(&self, ptr: NonNull<u8>, layout: Layout) -> BlockStatus {
        (**self).status(ptr, layout)
    }

    #[inline(always)]
    fn owns(&self, ptr: NonNull<u8>) -> bool {
        (**self).owns(ptr)
    }
}

#[cfg_attr(not(feature = "dev"), doc(hidden))]
pub fn base_try_dealloc_impl<
    T: ?Sized,
    D: DeallocChecked + ?Sized,
    F: FnOnce(&D, NonNull<T>, Layout),
>(
    d: &D,
    ptr: NonNull<T>,
    layout: Layout,
    succ: F,
) -> Result<(), AllocError> {
    let p = ptr.cast();
    match d.status(p, layout) {
        // SAFETY: the pointer is owned by us, and the layout is valid and non-zero-sized.
        BlockStatus::Owned => {
            succ(d, ptr, layout);
            Ok(())
        }
        other => AllocError::dealloc_failed(p, layout, other),
    }
}

/// Returns the maximum alignment satisfied by a non-null pointer.
#[must_use]
#[cfg_attr(not(feature = "dev"), doc(hidden))]
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
    /// The block status is unknown.
    Unknown,

    /// The block is neither owned by this allocator nor has an alignment matching the provided
    /// layout's.
    ///
    /// If `self.0` is `Some`, it's the maximum alignment the provided pointer fulfills.
    /// Otherwise, the implementation doesn't support returning the block's alignment.
    NotOwnedMisaligned(Option<usize>),

    /// The block isn't owned by this allocator.
    NotOwned,

    /// The block is owned by this allocator, but the provided pointer isn't the start of the
    /// block.
    ///
    /// If `self.0` is `Some`, it's the pointer to the start of the block.
    /// Otherwise, the implementation doesn't support returning the block's start, or an error
    /// occurred fetching it.
    OwnedNonHead(Option<NonNull<u8>>),

    /// The block is owned by this allocator, but the provided layout doesn't match the full block.
    ///
    /// If `self.0` is `Some`, it's the layout of the full block.
    /// Otherwise, the implementation doesn't support returning the block's full layout, or an error
    /// occurred fetching it.
    OwnedIncomplete(Option<Layout>),

    /// The block is owned by this allocator, but its alignment is less than the provided layout's.
    ///
    /// If `self.0` is `Some`, it's the maximum alignment the provided pointer fulfills.
    /// Otherwise, the implementation doesn't support returning the block's alignment.
    OwnedMisaligned(Option<usize>),

    /// The block is owned by this allocator.
    Owned,
}

impl Display for BlockStatus {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            BlockStatus::Unknown => write!(f, "unknown"),

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
